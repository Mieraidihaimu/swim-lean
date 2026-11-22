import SwimCore.Types
import SwimCore.Prng
import SwimCore.Wire
import SwimCore.Dissemination

namespace SwimCore

/-- Pure deterministic state machine representation of a SWIM node. -/
structure NodeState where
  selfId             : NodeId
  selfAddr           : PeerAddr
  incarnation        : Incarnation
  members            : Array MemberEntry
  disseminationBuf   : Array GossipUpdate
  prngState          : UInt64
  seqCounter         : UInt32
  protocolPeriodMs   : UInt64
  ackTimeoutMs       : UInt64
  suspectTimeoutMs   : UInt64
  nextProbeAt        : Timestamp
  probeIndex         : Nat
  pendingAckDeadline : Option (NodeId × UInt32 × Timestamp × Bool)
deriving Inhabited, Repr

/-- Initialize a SWIM node with cluster peers. -/
def initNode (id : NodeId) (addr : PeerAddr) (seed : UInt64) (peers : Array (NodeId × PeerAddr)) : NodeState :=
  let memberEntries := peers.filterMap fun (pId, pAddr) =>
    if pId == id then none
    else some {
      id := pId,
      addr := pAddr,
      status := MemberStatus.alive,
      incarnation := 0,
      suspectDeadline := 0
    }
  {
    selfId := id,
    selfAddr := addr,
    incarnation := 0,
    members := memberEntries,
    disseminationBuf := #[],
    prngState := seed,
    seqCounter := 0,
    protocolPeriodMs := 1000,
    ackTimeoutMs := 200,
    suspectTimeoutMs := 1000,
    nextProbeAt := 0,
    probeIndex := 0,
    pendingAckDeadline := none
  }

/-- Add a peer to the membership list if not self and not already present. -/
def NodeState.addPeer (st : NodeState) (id : NodeId) (addr : PeerAddr) : NodeState :=
  if id == st.selfId || st.members.any (fun m => m.id == id) then
    st
  else
    let entry : MemberEntry := {
      id := id,
      addr := addr,
      status := MemberStatus.alive,
      incarnation := 0,
      suspectDeadline := 0
    }
    { st with members := st.members.push entry }

def addPeer := NodeState.addPeer

/-- Remove a peer from the membership list. -/
def NodeState.removePeer (st : NodeState) (id : NodeId) : NodeState :=
  match st.members.findIdx? (fun m => m.id == id) with
  | some idx => { st with members := st.members.eraseIdx! idx }
  | none => st

def removePeer := NodeState.removePeer

/-- Look up a member entry by NodeId. -/
def NodeState.getMember? (st : NodeState) (id : NodeId) : Option MemberEntry :=
  st.members.find? (fun m => m.id == id)

def getMember? := NodeState.getMember?

/-- Transition a member to suspect state if currently alive. -/
def markSuspect (st : NodeState) (targetId : NodeId) (now : Timestamp) : NodeState × Array Action :=
  match st.members.findIdx? (fun m => m.id == targetId) with
  | some idx =>
    let m := st.members[idx]!
    if m.status == MemberStatus.alive then
      let m' := { m with
        status := MemberStatus.suspect,
        suspectDeadline := now + st.suspectTimeoutMs
      }
      let newMembers := st.members.set! idx m'
      let newBuf := addOrUpdate st.disseminationBuf targetId MemberStatus.suspect m.incarnation
      let act := Action.emitMembershipChange targetId MemberStatus.suspect m.incarnation
      ({ st with members := newMembers, disseminationBuf := newBuf }, #[act])
    else
      (st, #[])
  | none =>
    (st, #[])

/-- Scan membership array and promote expired suspect nodes to dead. -/
def checkSuspectTimeouts (st : NodeState) (now : Timestamp) : NodeState × Array Action :=
  Id.run do
    let mut curMembers := st.members
    let mut curBuf := st.disseminationBuf
    let mut acts : Array Action := #[]
    for i in [0:curMembers.size] do
      let m := curMembers[i]!
      if m.status == MemberStatus.suspect && now >= m.suspectDeadline then
        let m' := { m with status := MemberStatus.dead, suspectDeadline := 0 }
        curMembers := curMembers.set! i m'
        curBuf := addOrUpdate curBuf m.id MemberStatus.dead m.incarnation
        acts := acts.push (Action.emitMembershipChange m.id MemberStatus.dead m.incarnation)
    let nextSt := { st with members := curMembers, disseminationBuf := curBuf }
    (nextSt, acts)

/-- Merge incoming piggybacked gossip updates into local state.
    Refutes suspicion if self was suspected with incarnation >= local incarnation. -/
def mergeGossipUpdates (st : NodeState) (updates : Array GossipUpdate) (now : Timestamp) : NodeState × Array Action :=
  Id.run do
    let mut curSt := st
    let mut acts : Array Action := #[]
    for u in updates do
      if u.id == curSt.selfId then
        -- Update concerning local node: refute if suspected or marked dead with incarnation >= local
        if (u.status == MemberStatus.suspect || u.status == MemberStatus.dead) && u.incarnation >= curSt.incarnation then
          let newInc := u.incarnation + 1
          let newBuf := addOrUpdate curSt.disseminationBuf curSt.selfId MemberStatus.alive newInc
          curSt := { curSt with
            incarnation := newInc,
            disseminationBuf := newBuf
          }
          acts := acts.push (Action.emitMembershipChange curSt.selfId MemberStatus.alive newInc)
      else
        -- Update concerning a peer
        match curSt.members.findIdx? (fun m => m.id == u.id) with
        | some idx =>
          let cur := curSt.members[idx]!
          if shouldOverride u.incarnation u.status cur.incarnation cur.status then
            let newDeadline := if u.status == MemberStatus.suspect then now + curSt.suspectTimeoutMs else 0
            let m' := { cur with
              status := u.status,
              incarnation := u.incarnation,
              suspectDeadline := newDeadline
            }
            let newMembers := curSt.members.set! idx m'
            let newBuf := addOrUpdate curSt.disseminationBuf u.id u.status u.incarnation
            curSt := { curSt with
              members := newMembers,
              disseminationBuf := newBuf
            }
            acts := acts.push (Action.emitMembershipChange u.id u.status u.incarnation)
        | none =>
          -- Node not in membership list; record update in dissemination buffer
          let newBuf := addOrUpdate curSt.disseminationBuf u.id u.status u.incarnation
          curSt := { curSt with disseminationBuf := newBuf }
    (curSt, acts)

/-- Step transition handling periodic timer tick. -/
def stepTick (st : NodeState) (now : Timestamp) : NodeState × Array Action :=
  Id.run do
    let mut curSt := st
    let mut acts : Array Action := #[]

    -- 1. Check pending ACK deadline
    match curSt.pendingAckDeadline with
    | some (targetId, seq, deadline, isIndirect) =>
      if now >= deadline then
        if !isIndirect then
          -- Direct probe timed out: pick k random members and send pingReq
          let candidates := curSt.members.filter fun m =>
            m.id != targetId && m.id != curSt.selfId && m.status != MemberStatus.dead
          let k := 3
          let (selected, newPrng) := pickKRandom candidates k curSt.prngState
          curSt := { curSt with prngState := newPrng }
          if selected.isEmpty then
            -- No peers available for indirect probe: mark target suspect immediately
            let (st', suspectActs) := markSuspect curSt targetId now
            curSt := { st' with pendingAckDeadline := none }
            acts := acts ++ suspectActs
          else
            let maxTx := calculateMaxTransmissions 3 curSt.members.size
            let mut curBuf := curSt.disseminationBuf
            for helper in selected do
              let (updates, newBuf) := drainForPacket curBuf 6 maxTx
              curBuf := newBuf
              let msg := Message.pingReq curSt.selfId targetId seq updates
              acts := acts.push (Action.sendPacket helper.addr (encodeMessage msg))
            let nextDeadline := now + curSt.ackTimeoutMs
            curSt := { curSt with
              disseminationBuf := curBuf,
              pendingAckDeadline := some (targetId, seq, nextDeadline, true)
            }
        else
          -- Indirect probe timed out: mark target suspect and clear pending deadline
          let (st', suspectActs) := markSuspect curSt targetId now
          curSt := { st' with pendingAckDeadline := none }
          acts := acts ++ suspectActs
    | none => ()

    -- 2. Check suspect timeouts and promote to dead
    let (stAfterTimeouts, timeoutActs) := checkSuspectTimeouts curSt now
    curSt := stAfterTimeouts
    acts := acts ++ timeoutActs

    -- 3. Round-robin probe if no probe active and protocol period reached
    if curSt.pendingAckDeadline.isNone && now >= curSt.nextProbeAt then
      if curSt.members.isEmpty then
        curSt := { curSt with nextProbeAt := now + curSt.protocolPeriodMs }
      else
        let idx := curSt.probeIndex % curSt.members.size
        let target := curSt.members[idx]!
        let nextProbeIdx := curSt.probeIndex + 1
        let seq := curSt.seqCounter
        let nextSeq := seq + 1
        let maxTx := calculateMaxTransmissions 3 curSt.members.size
        let (updates, newBuf) := drainForPacket curSt.disseminationBuf 6 maxTx
        let msg := Message.ping curSt.selfId seq updates
        let bytes := encodeMessage msg
        acts := acts.push (Action.sendPacket target.addr bytes)
        curSt := { curSt with
          probeIndex := nextProbeIdx,
          seqCounter := nextSeq,
          disseminationBuf := newBuf,
          pendingAckDeadline := some (target.id, seq, now + curSt.ackTimeoutMs, false),
          nextProbeAt := now + curSt.protocolPeriodMs
        }

    return (curSt, acts)

/-- Step transition handling packet reception. -/
def stepRecvPacket (st : NodeState) (src : PeerAddr) (payload : ByteArray) (now : Timestamp) : NodeState × Array Action :=
  match decodeMessage payload with
  | none => (st, #[])
  | some msg =>
    Id.run do
      -- 1. Merge piggybacked gossip updates
      let updates := match msg with
        | .ping _ _ u => u
        | .ack _ _ u => u
        | .pingReq _ _ _ u => u
      let (st1, updateActs) := mergeGossipUpdates st updates now
      let mut acts := updateActs
      let mut curSt := st1

      -- 2. Process message according to type
      match msg with
      | .ping srcNodeId seq _ =>
        let maxTx := calculateMaxTransmissions 3 curSt.members.size
        let (piggyUpdates, newBuf) := drainForPacket curSt.disseminationBuf 6 maxTx
        let ackMsg := Message.ack curSt.selfId seq piggyUpdates
        let ackBytes := encodeMessage ackMsg
        let dstAddr := match curSt.members.find? (fun m => m.id == srcNodeId) with
          | some m => m.addr
          | none   => src
        acts := acts.push (Action.sendPacket dstAddr ackBytes)
        curSt := { curSt with disseminationBuf := newBuf }

      | .pingReq reqSrc targetId seq _ =>
        match curSt.members.find? (fun m => m.id == targetId) with
        | some targetMember =>
          let maxTx := calculateMaxTransmissions 3 curSt.members.size
          let (piggyUpdates, newBuf) := drainForPacket curSt.disseminationBuf 6 maxTx
          let forwardPing := Message.ping reqSrc seq piggyUpdates
          let pingBytes := encodeMessage forwardPing
          acts := acts.push (Action.sendPacket targetMember.addr pingBytes)
          curSt := { curSt with disseminationBuf := newBuf }
        | none => ()

      | .ack _ seq _ =>
        match curSt.pendingAckDeadline with
        | some (_, pendingSeq, _, _) =>
          if pendingSeq == seq then
            curSt := { curSt with pendingAckDeadline := none }
        | none => ()

      return (curSt, acts)

/-- Pure transition function driving the failure detector state machine. -/
def step (st : NodeState) (ev : Event) : NodeState × Array Action :=
  match ev with
  | .tick now => stepTick st now
  | .recvPacket src payload now => stepRecvPacket st src payload now

end SwimCore

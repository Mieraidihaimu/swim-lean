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
  pendingRelays      : Array (UInt32 × PeerAddr × UInt32)
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
    suspectTimeoutMs := 2500,
    nextProbeAt := 0,
    probeIndex := 0,
    pendingAckDeadline := none,
    pendingRelays := #[]
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

/-- Tail-recursive helper scanning membership entries `[i, curMembers.size)` to promote expired suspects.
    Avoids heap-allocating a `Range` object on every tick and enables Perceus in-place array updates. -/
def checkSuspectTimeoutsLoop (now : Timestamp) (i : Nat)
    (curMembers : Array MemberEntry) (curBuf : Array GossipUpdate) (acts : Array Action) :
    Array MemberEntry × Array GossipUpdate × Array Action :=
  if h : i < curMembers.size then
    let m := curMembers[i]
    if m.status == MemberStatus.suspect && now >= m.suspectDeadline then
      let m' := { m with status := MemberStatus.dead, suspectDeadline := 0 }
      let nextMembers := curMembers.set i m' h
      let nextBuf := addOrUpdate curBuf m.id MemberStatus.dead m.incarnation
      let nextActs := acts.push (Action.emitMembershipChange m.id MemberStatus.dead m.incarnation)
      checkSuspectTimeoutsLoop now (i + 1) nextMembers nextBuf nextActs
    else
      checkSuspectTimeoutsLoop now (i + 1) curMembers curBuf acts
  else
    (curMembers, curBuf, acts)
termination_by curMembers.size - i
decreasing_by
  all_goals (try simp only [Array.size_set]); omega

/-- Scan membership array and promote expired suspect nodes to dead. -/
def checkSuspectTimeouts (st : NodeState) (now : Timestamp) : NodeState × Array Action :=
  let members := st.members
  let buf := st.disseminationBuf
  let baseSt := { st with members := #[], disseminationBuf := #[] }
  let (nextMembers, nextBuf, acts) := checkSuspectTimeoutsLoop now 0 members buf #[]
  ({ baseSt with members := nextMembers, disseminationBuf := nextBuf }, acts)

/-- Merge a single incoming gossip update into `NodeState` (pure step for `mergeGossipUpdates`). -/
def mergeOneGossipUpdate (now : Timestamp) (acc : NodeState × Array Action) (u : GossipUpdate) :
    NodeState × Array Action :=
  let curSt := acc.1
  let acts := acc.2
  if u.id == curSt.selfId then
    -- Update concerning local node: refute if suspected or marked dead with incarnation >= local
    if (u.status == MemberStatus.suspect || u.status == MemberStatus.dead) && u.incarnation >= curSt.incarnation then
      -- Saturating increment prevents UInt32 wrap-around violating incarnation monotonicity
      let newInc := if u.incarnation < 0xFFFFFFFF then u.incarnation + 1 else u.incarnation
      let newBuf := addOrUpdate curSt.disseminationBuf curSt.selfId MemberStatus.alive newInc
      let nextSt := { curSt with
        incarnation := newInc,
        disseminationBuf := newBuf
      }
      (nextSt, acts.push (Action.emitMembershipChange nextSt.selfId MemberStatus.alive newInc))
    else
      (curSt, acts)
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
        let members := curSt.members
        let buf := curSt.disseminationBuf
        let baseSt := { curSt with members := #[], disseminationBuf := #[] }
        let newMembers := members.set! idx m'
        let newBuf := addOrUpdate buf u.id u.status u.incarnation
        let nextSt := { baseSt with
          members := newMembers,
          disseminationBuf := newBuf
        }
        (nextSt, acts.push (Action.emitMembershipChange u.id u.status u.incarnation))
      else
        (curSt, acts)
    | none =>
      -- Node not in membership list; record update in dissemination buffer
      let newBuf := addOrUpdate curSt.disseminationBuf u.id u.status u.incarnation
      ({ curSt with disseminationBuf := newBuf }, acts)

/-- Merge incoming piggybacked gossip updates into local state.
    Refutes suspicion if self was suspected with incarnation >= local incarnation. -/
def mergeGossipUpdates (st : NodeState) (updates : Array GossipUpdate) (now : Timestamp) : NodeState × Array Action :=
  updates.foldl (mergeOneGossipUpdate now) (st, #[])

/-- Compute the earliest monotonic timestamp (ms) at which the node needs a timer tick.
    Used by the C runtime (`epoll`/`poll`) to avoid unnecessary wakeups. -/
def nextWakeupAt (st : NodeState) : Timestamp :=
  let d1 := match st.pendingAckDeadline with
    | some (_, _, deadline, _) => deadline
    | none => st.nextProbeAt
  st.members.foldl (fun acc m =>
    if m.status == MemberStatus.suspect && m.suspectDeadline > 0 then
      min acc m.suspectDeadline
    else acc) d1

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
          let relaySeq := curSt.seqCounter
          let reqAddr := match curSt.members.find? (fun m => m.id == reqSrc) with
            | some rm => rm.addr
            | none    => src
          let forwardPing := Message.ping curSt.selfId relaySeq piggyUpdates
          let pingBytes := encodeMessage forwardPing
          acts := acts.push (Action.sendPacket targetMember.addr pingBytes)
          let baseRelays := if curSt.pendingRelays.size >= 32 then
              curSt.pendingRelays.extract 1 curSt.pendingRelays.size
            else curSt.pendingRelays
          let nextRelays := baseRelays.push (relaySeq, reqAddr, seq)
          curSt := { curSt with
            disseminationBuf := newBuf,
            seqCounter := relaySeq + 1,
            pendingRelays := nextRelays
          }
        | none => ()

      | .ack ackSrc seq _ =>
        match curSt.pendingAckDeadline with
        | some (_, pendingSeq, _, _) =>
          if pendingSeq == seq then
            curSt := { curSt with pendingAckDeadline := none }
        | none => ()
        match curSt.pendingRelays.findIdx? (fun (relaySeq, _, _) => relaySeq == seq) with
        | some idx =>
          let (_, reqAddr, origSeq) := curSt.pendingRelays[idx]!
          let nextRelays := curSt.pendingRelays.eraseIdx! idx
          let maxTx := calculateMaxTransmissions 3 curSt.members.size
          let (piggyUpdates, newBuf) := drainForPacket curSt.disseminationBuf 6 maxTx
          let relayAck := Message.ack ackSrc origSeq piggyUpdates
          acts := acts.push (Action.sendPacket reqAddr (encodeMessage relayAck))
          curSt := { curSt with disseminationBuf := newBuf, pendingRelays := nextRelays }
        | none => ()

      return (curSt, acts)

/-- Pure transition function driving the failure detector state machine. -/
def step (st : NodeState) (ev : Event) : NodeState × Array Action :=
  match ev with
  | .tick now => stepTick st now
  | .recvPacket src payload now => stepRecvPacket st src payload now

end SwimCore

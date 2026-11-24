import SwimCore

open SwimCore

/-- In-flight UDP packet in the deterministic discrete-event simulator. -/
structure SimPacket where
  src       : PeerAddr
  dst       : PeerAddr
  payload   : ByteArray
  deliverAt : Timestamp
  deriving Inhabited

/-- Configuration for a deterministic simulation scenario. -/
structure SimConfig where
  name            : String
  numNodes        : Nat
  durationMs      : Timestamp
  stepGranMs      : Timestamp := 20
  seed            : UInt64 := 0x9E3779B97F4A7C15
  packetLossPct   : UInt32 := 0
  crashAtMs       : Option (Timestamp × Nat) := none
  blockLink       : PeerAddr → PeerAddr → Bool := fun _ _ => false

/-- Metrics collected during a deterministic simulation run. -/
structure SimMetrics where
  nodes              : Array NodeState
  packetsSent        : Nat
  packetsDelivered   : Nat
  packetsDropped     : Nat
  membershipEvents   : Nat
  pingReqCount       : Nat
  firstDetectMs      : Option Timestamp
  fullConvergeMs     : Option Timestamp
  maxAliveFalseDead  : Nat

private def addrFor (idx : Nat) (basePort : UInt16 := 9001) : PeerAddr :=
  { ip := 0x7F000001, port := basePort + idx.toUInt16 }

private def initCluster (n : Nat) (seed : UInt64) (basePort : UInt16 := 9001) : Array NodeState :=
  Id.run do
    let mut nodes : Array NodeState := #[]
    for i in [0:n] do
      let id : NodeId := i.toUInt32 + 1
      let addr := addrFor i basePort
      let nodeSeed := seed ^^^ (i.toUInt64 + 1) * 0xBF58476D1CE4E5B9
      let peers : Array (NodeId × PeerAddr) := Id.run do
        let mut p := #[]
        for j in [0:n] do
          if j != i then
            p := p.push (j.toUInt32 + 1, addrFor j basePort)
        p
      let (shuffledPeers, seedAfterShuffle) := shuffleArray peers nodeSeed
      let mut st := initNode id addr seedAfterShuffle shuffledPeers
      -- Stagger initial probe phase deterministically to mimic real asynchronous startup
      st := { st with nextProbeAt := (i.toUInt64 * (st.protocolPeriodMs / max 1 n.toUInt64)) }
      nodes := nodes.push st
    nodes

private def runSim (cfg : SimConfig) : SimMetrics :=
  Id.run do
    let mut nodes := initCluster cfg.numNodes cfg.seed
    let mut crashed : Array Bool := Array.replicate cfg.numNodes false
    let mut queue : Array SimPacket := #[]
    let mut prng := cfg.seed
    let mut now : Timestamp := 0
    let mut sent : Nat := 0
    let mut dropped : Nat := 0
    let mut membershipEvs : Nat := 0
    let mut pingReqs : Nat := 0
    let mut firstDetect : Option Timestamp := none
    let mut fullConverge : Option Timestamp := none

    let enqueueActions := fun (srcAddr : PeerAddr) (acts : Array Action) (curNow : Timestamp)
        (curQueue : Array SimPacket) (curPrng : UInt64) (curSent curDropped curEvs curPingReq : Nat) =>
      Id.run do
        let mut q := curQueue
        let mut rng := curPrng
        let mut s := curSent
        let mut dr := curDropped
        let mut evs := curEvs
        let mut prq := curPingReq
        for act in acts do
          match act with
          | Action.sendPacket dst payload =>
            s := s + 1
            if payload.size > 0 && payload.get! 0 == 3 then
              prq := prq + 1
            let (roll, rng1) := randomRange rng 0 99
            let (lat, rng2) := randomRange rng1 5 25
            rng := rng2
            if cfg.blockLink srcAddr dst || roll < cfg.packetLossPct then
              dr := dr + 1
            else
              q := q.push {
                src := srcAddr,
                dst := dst,
                payload := payload,
                deliverAt := curNow + lat.toUInt64
              }
          | Action.emitMembershipChange _ _ _ =>
            evs := evs + 1
        return (q, rng, s, dr, evs, prq)

    while now < cfg.durationMs do
      now := now + cfg.stepGranMs

      -- Trigger injected node crash if scheduled
      match cfg.crashAtMs with
      | some (crashTime, crashIdx) =>
        if now >= crashTime && crashIdx < crashed.size then
          crashed := crashed.set! crashIdx true
      | none => ()

      -- 1. Deliver all due in-flight packets first (preserving reply delivery across steps)
      let mut remaining : Array SimPacket := #[]
      let mut due : Array SimPacket := #[]
      for pkt in queue do
        if pkt.deliverAt <= now then
          due := due.push pkt
        else
          remaining := remaining.push pkt
      queue := remaining

      for pkt in due do
        for i in [0:nodes.size] do
          if !crashed[i]! then
            let st := nodes[i]!
            if st.selfAddr == pkt.dst then
              let (st', acts) := step st (Event.recvPacket pkt.src pkt.payload now)
              nodes := nodes.set! i st'
              let (q', r', s', dr', evs', prq') :=
                enqueueActions st.selfAddr acts now queue prng sent dropped membershipEvs pingReqs
              queue := q'; prng := r'; sent := s'; dropped := dr'; membershipEvs := evs'; pingReqs := prq'

      -- 2. Advance each living node's timer tick
      for i in [0:nodes.size] do
        if !crashed[i]! then
          let st := nodes[i]!
          let (st', acts) := step st (Event.tick now)
          nodes := nodes.set! i st'
          let (q', r', s', dr', evs', prq') :=
            enqueueActions st.selfAddr acts now queue prng sent dropped membershipEvs pingReqs
          queue := q'; prng := r'; sent := s'; dropped := dr'; membershipEvs := evs'; pingReqs := prq'

      -- 3. Track failure-detection and cluster convergence timestamps when a node was crashed
      match cfg.crashAtMs with
      | some (_, crashIdx) =>
        let targetId : NodeId := crashIdx.toUInt32 + 1
        let mut anyDetected := false
        let mut allDead := true
        for i in [0:nodes.size] do
          if !crashed[i]! then
            match nodes[i]!.getMember? targetId with
            | some m =>
              if m.status != MemberStatus.alive then
                anyDetected := true
              if m.status != MemberStatus.dead then
                allDead := false
            | none => allDead := false
        if anyDetected && firstDetect.isNone then
          firstDetect := some now
        if allDead && fullConverge.isNone then
          fullConverge := some now
      | none => ()

    -- Count any healthy surviving nodes falsely marked dead by any surviving peer
    let mut falseDead := 0
    for i in [0:nodes.size] do
      if !crashed[i]! then
        let st := nodes[i]!
        for j in [0:nodes.size] do
          if i != j && !crashed[j]! then
            let peerId : NodeId := j.toUInt32 + 1
            match st.getMember? peerId with
            | some m =>
              if m.status == MemberStatus.dead then
                falseDead := falseDead + 1
            | none => ()

    {
      nodes := nodes,
      packetsSent := sent,
      packetsDelivered := sent - dropped,
      packetsDropped := dropped,
      membershipEvents := membershipEvs,
      pingReqCount := pingReqs,
      firstDetectMs := firstDetect,
      fullConvergeMs := fullConverge,
      maxAliveFalseDead := falseDead
    }

private def countAliveStatus (nodes : Array NodeState) (targetId : NodeId) (expected : MemberStatus) : Nat :=
  Id.run do
    let mut c : Nat := 0
    for st in nodes do
      if st.selfId != targetId then
        match st.getMember? targetId with
        | some m => if m.status == expected then c := c + 1
        | none => ()
    return c

def main : IO UInt32 := do
  IO.println "=== SWIM Deterministic Simulation Testing (SplitMix64 DST) ==="

  -- Suite 1: Healthy 8-node cluster (zero false positives)
  let s1 := runSim {
    name := "Healthy Baseline",
    numNodes := 8,
    durationMs := 10000,
    seed := 0x1111222233334444
  }
  IO.println s!"[Suite 1] 8-Node Healthy Baseline: sent={s1.packetsSent}, events={s1.membershipEvents}, falseDead={s1.maxAliveFalseDead}"
  if s1.maxAliveFalseDead != 0 || s1.packetsSent == 0 then
    IO.eprintln "FAIL [Suite 1]: Expected zero false dead assertions and nonzero traffic."
    return 1

  -- Suite 2: 12-node crash detection & dissemination convergence
  let s2 := runSim {
    name := "Crash Convergence",
    numNodes := 12,
    durationMs := 12000,
    seed := 0x2222333344445555,
    crashAtMs := some (2000, 11) -- crash Node 12 at t=2000ms
  }
  let deadSeen := countAliveStatus s2.nodes 12 MemberStatus.dead
  IO.println s!"[Suite 2] 12-Node Crash Detection (Node 12 killed @2000ms): deadObservers={deadSeen}/11, firstDetect={s2.firstDetectMs}ms, fullConverge={s2.fullConvergeMs}ms, falseDead={s2.maxAliveFalseDead}"
  if deadSeen != 11 || s2.maxAliveFalseDead != 0 then
    IO.eprintln s!"FAIL [Suite 2]: Expected 11/11 observers marking Node 12 DEAD (got {deadSeen}), falseDead={s2.maxAliveFalseDead}."
    return 1

  -- Suite 3: Asymmetric unidirectional drop (1 -> 2 blocked), proving indirect pingReq keeps Node 2 alive
  let s3 := runSim {
    name := "Asymmetric Link PingReq",
    numNodes := 6,
    durationMs := 8000,
    seed := 0x3333444455556666,
    blockLink := fun src dst => src.port == 9001 && dst.port == 9002
  }
  let node1Sees2 := s3.nodes[0]!.getMember? 2 |>.map (·.status)
  IO.println s!"[Suite 3] Asymmetric Drop (1->2 blocked): sent={s3.packetsSent}, pingReqs={s3.pingReqCount}, Node 1 view of Node 2={repr node1Sees2}, falseDead={s3.maxAliveFalseDead}"
  if s3.maxAliveFalseDead > 0 then
    for st in s3.nodes do
      for m in st.members do
        if m.status != MemberStatus.alive then
          IO.println s!"  [Suite 3 detail] Node {st.selfId} sees Node {m.id} as {repr m.status} (inc={m.incarnation})"
  if s3.pingReqCount == 0 || node1Sees2 != some MemberStatus.alive || s3.maxAliveFalseDead != 0 then
    IO.eprintln s!"FAIL [Suite 3]: Expected indirect pingReq recovery keeping Node 2 alive (got {repr node1Sees2}, pingReqs={s3.pingReqCount})."
    return 1

  -- Suite 4: 10-node tolerance under 10% random UDP loss
  let s4 := runSim {
    name := "10% Packet Loss Tolerance",
    numNodes := 10,
    durationMs := 10000,
    seed := 0x4444555566667777,
    packetLossPct := 10
  }
  IO.println s!"[Suite 4] 10-Node 10% Packet Loss: sent={s4.packetsSent}, dropped={s4.packetsDropped}, pingReqs={s4.pingReqCount}, falseDead={s4.maxAliveFalseDead}"
  if s4.packetsDropped == 0 || s4.maxAliveFalseDead > 2 then
    IO.eprintln s!"FAIL [Suite 4]: Excessive false positives under 10% packet loss: falseDead={s4.maxAliveFalseDead}."
    return 1

  -- Suite 5: Empirical O(log n) dissemination scaling across N = 8, 16, 32, 64
  IO.println "\n[Suite 5] Empirical O(log N) Dissemination Convergence Scaling:"
  IO.println "   N | ceil(log2 N) | detectMs | convergeMs | spreadMs | approxRounds"
  for n in [8, 16, 32, 64] do
    let m := runSim {
      name := s!"Scale-{n}",
      numNodes := n,
      durationMs := 18000,
      seed := 0x5555666677778888 + n.toUInt64,
      crashAtMs := some (2000, n - 1)
    }
    let observers := countAliveStatus m.nodes n.toUInt32 MemberStatus.dead
    let det := m.firstDetectMs.getD 0
    let conv := m.fullConvergeMs.getD 0
    let spread := if conv >= det then conv - det else 0
    let rounds := (spread + 999) / 1000
    let logN := ceilLog2 n
    IO.println s!"  {n} | {logN}            | {det}     | {conv}       | {spread}     | {rounds}"
    if observers != n - 1 || m.maxAliveFalseDead != 0 then
      IO.eprintln s!"FAIL [Suite 5]: N={n} expected {n - 1}/{n - 1} dead observers, got {observers}, falseDead={m.maxAliveFalseDead}."
      return 1

  IO.println "\nAll 5 SWIM Deterministic Simulation Testing (DST) suites PASSED!"
  return 0

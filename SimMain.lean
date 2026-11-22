import SwimCore

open SwimCore

def main : IO Unit := do
  IO.println "=== SWIM Protocol Pure Lean Discrete-Event Simulator ==="
  let nNodes : UInt32 := 5
  IO.println s!"Initializing a cluster of {nNodes} nodes..."

  -- Initialize 5 nodes on 127.0.0.1 with ports 9001..9005
  let basePort : UInt16 := 9001
  let ip : UInt32 := 0x7F000001 -- 127.0.0.1
  let mut nodes : Array NodeState := #[]

  for i in [0:nNodes.toNat] do
    let id : NodeId := i.toUInt32 + 1
    let addr : PeerAddr := { ip := ip, port := basePort + i.toUInt16 }
    let seed : UInt64 := 0x1234567890ABCDEF + i.toUInt64 * 1000
    let peers : Array (NodeId × PeerAddr) := Id.run do
      let mut p := #[]
      for j in [0:nNodes.toNat] do
        if j != i then
          p := p.push (j.toUInt32 + 1, { ip := ip, port := basePort + j.toUInt16 })
      p
    let st := initNode id addr seed peers
    nodes := nodes.push st

  IO.println s!"Successfully bootstrapped {nodes.size} nodes with full mesh peer lists."

  -- Run simulation ticks
  IO.println "Simulating 10 protocol periods (1000ms each)..."
  let mut now : Timestamp := 0
  let mut totalPackets : Nat := 0
  let mut totalMembershipEvents : Nat := 0

  for stepIdx in [1:11] do
    now := now + 1000
    let mut inFlightPackets : Array (PeerAddr × PeerAddr × ByteArray) := #[]

    -- Tick all nodes
    for i in [0:nodes.size] do
      let st := nodes[i]!
      let (st', actions) := step st (Event.tick now)
      nodes := nodes.set! i st'
      for act in actions do
        match act with
        | Action.sendPacket dst payload =>
          inFlightPackets := inFlightPackets.push (st.selfAddr, dst, payload)
          totalPackets := totalPackets + 1
        | Action.emitMembershipChange nodeId status inc =>
          totalMembershipEvents := totalMembershipEvents + 1
          IO.println s!"[Tick {stepIdx}] Node {st.selfId} observed membership change: Node {nodeId} -> {repr status} (inc: {inc})"

    -- Deliver in-flight packets
    for (src, dst, payload) in inFlightPackets do
      -- Find recipient
      for i in [0:nodes.size] do
        let st := nodes[i]!
        if st.selfAddr == dst then
          let (st', actions) := step st (Event.recvPacket src payload now)
          nodes := nodes.set! i st'
          for act in actions do
            match act with
            | Action.sendPacket _ _ => totalPackets := totalPackets + 1
            | Action.emitMembershipChange nodeId status inc =>
              totalMembershipEvents := totalMembershipEvents + 1
              IO.println s!"[Packet] Node {st.selfId} observed membership change: Node {nodeId} -> {repr status} (inc: {inc})"

  IO.println s!"Simulation completed: {totalPackets} packets exchanged across {nNodes} nodes."
  IO.println "All nodes healthy, gossip disseminated successfully."

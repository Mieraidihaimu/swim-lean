import SwimCore.Types

namespace SwimCore

/-- Determines whether an incoming update dominates and should override an existing update.
    Dominance rules:
    1. Higher incarnation strictly dominates lower incarnation.
    2. At equal incarnation: `dead` dominates `suspect` and `alive`, `suspect` dominates `alive`.
    3. Identical incarnation and status do not override (preventing redundant resets of transmission counters). -/
def shouldOverride (newInc : Incarnation) (newSt : MemberStatus) (curInc : Incarnation) (curSt : MemberStatus) : Bool :=
  if newInc > curInc then
    true
  else if newInc == curInc then
    match curSt, newSt with
    | .alive, .suspect => true
    | .alive, .dead    => true
    | .suspect, .dead  => true
    | _, _             => false
  else
    false

/-- Add or update a gossip update in the dissemination buffer.
    - If node is already present in buffer: override if new incarnation is strictly higher,
      or if equal incarnation and incoming status is Suspect/Dead overriding Alive (or Dead overriding Suspect).
      Resets transmission counter to 0 if updated.
    - If not present: insert new update with transmission counter 0.
    In-place array updates with no unnecessary copying. -/
def addOrUpdate (buf : Array GossipUpdate) (id : NodeId) (status : MemberStatus) (incarnation : Incarnation) : Array GossipUpdate :=
  match buf.findIdx? (fun u => u.id == id) with
  | some idx =>
    let cur := buf[idx]!
    if shouldOverride incarnation status cur.incarnation cur.status then
      buf.set! idx { id := id, status := status, incarnation := incarnation, transmissions := 0 }
    else
      buf
  | none =>
    buf.push { id := id, status := status, incarnation := incarnation, transmissions := 0 }

/-- Increment transmission count safely clamped to UInt8 max (255) to prevent overflow. -/
def nextTransmissions (t : UInt8) : UInt8 :=
  if t < 255 then t + 1 else 255

/-- Drain up to `maxCount` updates from the dissemination buffer for piggybacking onto an outgoing packet.
    Returns: `(updatesToSend, remainingBuf)`.
    - Selects up to `maxCount` updates from the buffer.
    - Increments their `transmissions` count.
    - Drops any update whose transmission count reaches or exceeds `maxTransmissions`
      (where `maxTransmissions` is typically λ ⌈log₂ n⌉).
    - Retains unselected updates and re-enqueues retained updates in fair round-robin order.
    Ensures in-place array updates with no unnecessary copying. -/
def drainForPacket (buf : Array GossipUpdate) (maxCount : Nat) (maxTransmissions : UInt8) : (Array GossipUpdate × Array GossipUpdate) :=
  Id.run do
    let k := min maxCount buf.size
    let mut toSend := Array.mkEmpty k
    let mut retained := Array.mkEmpty k
    for i in [0:k] do
      let u := buf[i]!
      let newTx := nextTransmissions u.transmissions
      let u' := { u with transmissions := newTx }
      toSend := toSend.push u'
      if newTx < maxTransmissions then
        retained := retained.push u'
    let mut remaining := Array.mkEmpty (buf.size - k + retained.size)
    for i in [k:buf.size] do
      let u := buf[i]!
      if u.transmissions < maxTransmissions then
        remaining := remaining.push u
    for u in retained do
      remaining := remaining.push u
    (toSend, remaining)

/-- Ceiling of base-2 logarithm for `n : Nat`. For `n <= 1`, returns 0. -/
def ceilLog2 (n : Nat) : Nat :=
  if n <= 1 then 0 else Nat.log2 (n - 1) + 1

/-- Compute maximum transmission count bound: λ ⌈log₂ n⌉.
    Ensures at least `lambda` (or 1) transmission for small cluster sizes. -/
def calculateMaxTransmissions (lambda : Nat) (clusterSize : Nat) : UInt8 :=
  let c := ceilLog2 clusterSize
  let multiplier := if c == 0 then 1 else c
  let limit := lambda * multiplier
  UInt8.ofNat (min 255 limit)

/-- Check if the buffer contains an update for a given node id. -/
def contains (buf : Array GossipUpdate) (id : NodeId) : Bool :=
  buf.any (fun u => u.id == id)

/-- Find an update in the buffer by node id. -/
def find? (buf : Array GossipUpdate) (id : NodeId) : Option GossipUpdate :=
  buf.find? (fun u => u.id == id)

/-- Remove an update for a specific node from the dissemination buffer if present. -/
def remove (buf : Array GossipUpdate) (id : NodeId) : Array GossipUpdate :=
  match buf.findIdx? (fun u => u.id == id) with
  | some idx => buf.eraseIdx! idx
  | none => buf

/-- Empty the dissemination buffer. -/
def clear (_buf : Array GossipUpdate) : Array GossipUpdate :=
  #[]

end SwimCore

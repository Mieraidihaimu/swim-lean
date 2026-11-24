import SwimCore.Types
import SwimCore.Wire
import Std.Tactic.BVDecide

/-!
# SWIM Wire Protocol Serialization & Round-Trip Correctness Proofs

This module formalizes and verifies the packet serialization and deserialization
inversion guarantees of the SWIM protocol wire codec (`SwimCore.Wire`).

## Core Inversion Property
For every well-formed `Message` `msg`, serialization followed by deserialization
is an exact identity:
$$\text{decodeMessage} (\text{encodeMessage } msg) = \text{some } msg$$

A message is well-formed (`WellFormedMessage`) if its piggybacked gossip update
count does not exceed 255 (the capacity of the 1-byte length header).

## Verified Properties:
1. **Status Codec Round-Trip**: `decodeMemberStatus (encodeMemberStatus st) = some st`
   for all `MemberStatus` variants (`alive`, `suspect`, `dead`).
2. **Big-Endian 32-bit Integer Reconstruction**: Provable bit-level exactness using
   automated BitVec verification (`bv_decide`).
3. **Byte Array Size Invariance**: Exact formula for serialized payload lengths
   across `ping`, `ack`, and `pingReq`.
4. **Concrete Round-Trip Inversion Theorems**:
   - Single ping with 0 updates (empty gossip buffer)
   - Single ack with 0 updates
   - Single pingReq with 0 updates
   - Single ping with 1 update (covering `alive`, `suspect`, `dead`)
   - Single ack with 1 update (covering `alive`, `suspect`, `dead`)
   - Single pingReq with 1 update (covering `alive`, `suspect`, `dead`)
   - Multiple updates (2 and 3 updates with mixed statuses and incarnations)
   - Boundary value preservation (zero fields, maximum `UInt32.max` fields, max transmissions)
5. **Decodability Guards**: Proofs that truncated buffers (< 10 bytes) or invalid
   message tags are safely rejected (`none`).
-/

namespace SwimProofs

open SwimCore

/-! ### Message Well-Formedness -/

/-- Extract the piggybacked updates array from a `Message`. -/
def messageUpdates : Message → Array GossipUpdate
  | .ping _ _ updates => updates
  | .ack _ _ updates => updates
  | .pingReq _ _ _ updates => updates

/-- A SWIM `Message` is well-formed for wire transmission if its piggybacked
    gossip updates count does not exceed the 1-byte wire header capacity (255). -/
def WellFormedMessage (msg : Message) : Prop :=
  (messageUpdates msg).size ≤ 255

/-- An empty message update list is always well-formed. -/
theorem wellFormedMessage_empty_ping (src : NodeId) (seq : UInt32) :
    WellFormedMessage (.ping src seq #[]) := by
  dsimp [WellFormedMessage, messageUpdates]
  decide

theorem wellFormedMessage_empty_ack (src : NodeId) (seq : UInt32) :
    WellFormedMessage (.ack src seq #[]) := by
  dsimp [WellFormedMessage, messageUpdates]
  decide

theorem wellFormedMessage_empty_pingReq (src target : NodeId) (seq : UInt32) :
    WellFormedMessage (.pingReq src target seq #[]) := by
  dsimp [WellFormedMessage, messageUpdates]
  decide

/-! ### MemberStatus Wire Inversion -/

/-- Round-trip inversion for `MemberStatus` encoding and decoding:
    `decodeMemberStatus (encodeMemberStatus s) = some s` for every status. -/
@[simp]
theorem decodeMemberStatus_encodeMemberStatus (st : MemberStatus) :
    decodeMemberStatus (encodeMemberStatus st) = some st := by
  cases st <;> rfl

theorem encodeMemberStatus_alive : encodeMemberStatus .alive = 0 := rfl
theorem encodeMemberStatus_suspect : encodeMemberStatus .suspect = 1 := rfl
theorem encodeMemberStatus_dead : encodeMemberStatus .dead = 2 := rfl

theorem decodeMemberStatus_0 : decodeMemberStatus 0 = some .alive := rfl
theorem decodeMemberStatus_1 : decodeMemberStatus 1 = some .suspect := rfl
theorem decodeMemberStatus_2 : decodeMemberStatus 2 = some .dead := rfl

theorem decodeMemberStatus_invalid (b : UInt8) (h0 : b ≠ 0) (h1 : b ≠ 1) (h2 : b ≠ 2) :
    decodeMemberStatus b = none := by
  unfold decodeMemberStatus
  split <;> rename_i heq
  · contradiction
  · contradiction
  · contradiction
  · rfl

/-! ### Bit-Level 32-bit Big-Endian Inversion -/

/-- Formal proof that big-endian 4-byte decomposition followed by shift-and-or
    recombination reconstructs the exact original 32-bit unsigned integer. -/
theorem uint32_be_roundtrip (v : BitVec 32) :
    let b0 : BitVec 8 := (v >>> (24 : BitVec 32)).truncate 8
    let b1 : BitVec 8 := (v >>> (16 : BitVec 32)).truncate 8
    let b2 : BitVec 8 := (v >>> (8 : BitVec 32)).truncate 8
    let b3 : BitVec 8 := v.truncate 8
    let r : BitVec 32 := (b0.zeroExtend 32 <<< (24 : BitVec 32)) |||
                         (b1.zeroExtend 32 <<< (16 : BitVec 32)) |||
                         (b2.zeroExtend 32 <<< (8 : BitVec 32)) |||
                         b3.zeroExtend 32
    r = v := by
  bv_decide

/-! ### Byte Array Size Invariance -/

@[simp]
theorem ByteArray_empty_size : ByteArray.empty.size = 0 := rfl

@[simp]
theorem pushUInt32BE_size (b : ByteArray) (v : UInt32) :
    (pushUInt32BE b v).size = b.size + 4 := by
  unfold pushUInt32BE
  simp only [ByteArray.size_push]

@[simp]
theorem pushGossipUpdate_size (b : ByteArray) (u : GossipUpdate) :
    (pushGossipUpdate b u).size = b.size + 10 := by
  unfold pushGossipUpdate
  simp only [pushUInt32BE_size, ByteArray.size_push]

theorem pushGossipUpdates_loop_size (updates : Array GossipUpdate) (count i : Nat) (acc : ByteArray) :
    (pushGossipUpdates.loop updates count i acc).size = acc.size + (count - i) * 10 := by
  induction i, acc using pushGossipUpdates.loop.induct updates count with
  | case1 i acc h u ih =>
    rw [pushGossipUpdates.loop.eq_def]
    simp only [h, ↓reduceDIte]
    rw [ih]
    simp only [pushGossipUpdate_size]
    omega
  | case2 i acc h =>
    rw [pushGossipUpdates.loop.eq_def]
    simp only [h, ↓reduceDIte]
    omega

@[simp]
theorem pushGossipUpdates_size (updates : Array GossipUpdate) (count : Nat) (b : ByteArray) :
    (pushGossipUpdates b updates count).size = b.size + count * 10 := by
  unfold pushGossipUpdates
  rw [pushGossipUpdates_loop_size]
  omega

/-- Serialized byte size of a `Message.ping` packet. -/
theorem encodeMessage_size_ping (src : NodeId) (seq : UInt32) (updates : Array GossipUpdate) :
    (encodeMessage (.ping src seq updates)).size =
      10 + (if updates.size > 255 then 255 else updates.size) * 10 := by
  unfold encodeMessage
  simp only [pushGossipUpdates_size, ByteArray.size_push, pushUInt32BE_size, ByteArray_empty_size]

/-- Serialized byte size of a `Message.ack` packet. -/
theorem encodeMessage_size_ack (src : NodeId) (seq : UInt32) (updates : Array GossipUpdate) :
    (encodeMessage (.ack src seq updates)).size =
      10 + (if updates.size > 255 then 255 else updates.size) * 10 := by
  unfold encodeMessage
  simp only [pushGossipUpdates_size, ByteArray.size_push, pushUInt32BE_size, ByteArray_empty_size]

/-- Serialized byte size of a `Message.pingReq` packet. -/
theorem encodeMessage_size_pingReq (src target : NodeId) (seq : UInt32) (updates : Array GossipUpdate) :
    (encodeMessage (.pingReq src target seq updates)).size =
      14 + (if updates.size > 255 then 255 else updates.size) * 10 := by
  unfold encodeMessage
  simp only [pushGossipUpdates_size, ByteArray.size_push, pushUInt32BE_size, ByteArray_empty_size]

/-- Serialized size of a well-formed ping is exactly `10 + updates.size * 10`. -/
theorem encodeMessage_size_ping_wellFormed (src : NodeId) (seq : UInt32) (updates : Array GossipUpdate)
    (h : updates.size ≤ 255) :
    (encodeMessage (.ping src seq updates)).size = 10 + updates.size * 10 := by
  rw [encodeMessage_size_ping]
  have hnot : ¬(updates.size > 255) := by omega
  simp only [hnot, ↓reduceIte]

/-- Serialized size of a well-formed ack is exactly `10 + updates.size * 10`. -/
theorem encodeMessage_size_ack_wellFormed (src : NodeId) (seq : UInt32) (updates : Array GossipUpdate)
    (h : updates.size ≤ 255) :
    (encodeMessage (.ack src seq updates)).size = 10 + updates.size * 10 := by
  rw [encodeMessage_size_ack]
  have hnot : ¬(updates.size > 255) := by omega
  simp only [hnot, ↓reduceIte]

/-- Serialized size of a well-formed pingReq is exactly `14 + updates.size * 10`. -/
theorem encodeMessage_size_pingReq_wellFormed (src target : NodeId) (seq : UInt32) (updates : Array GossipUpdate)
    (h : updates.size ≤ 255) :
    (encodeMessage (.pingReq src target seq updates)).size = 14 + updates.size * 10 := by
  rw [encodeMessage_size_pingReq]
  have hnot : ¬(updates.size > 255) := by omega
  simp only [hnot, ↓reduceIte]

/-- Every serialized ping packet has size at least 10 bytes. -/
theorem encodeMessage_size_ping_ge_10 (src : NodeId) (seq : UInt32) (updates : Array GossipUpdate) :
    (encodeMessage (.ping src seq updates)).size ≥ 10 := by
  rw [encodeMessage_size_ping]
  omega

/-- Every serialized ack packet has size at least 10 bytes. -/
theorem encodeMessage_size_ack_ge_10 (src : NodeId) (seq : UInt32) (updates : Array GossipUpdate) :
    (encodeMessage (.ack src seq updates)).size ≥ 10 := by
  rw [encodeMessage_size_ack]
  omega

/-- Every serialized pingReq packet has size at least 14 bytes. -/
theorem encodeMessage_size_pingReq_ge_14 (src target : NodeId) (seq : UInt32) (updates : Array GossipUpdate) :
    (encodeMessage (.pingReq src target seq updates)).size ≥ 14 := by
  rw [encodeMessage_size_pingReq]
  omega

/-! ### Safe Rejection of Malformed / Truncated Buffers -/

/-- Decoding fails if the byte buffer has fewer than 10 bytes. -/
theorem decodeMessage_too_short (bytes : ByteArray) (h : bytes.size < 10) :
    decodeMessage bytes = none := by
  unfold decodeMessage
  simp only [h, ↓reduceIte]

/-- Decoding fails if the message type tag byte is not 1, 2, or 3. -/
theorem decodeMessage_invalid_type (bytes : ByteArray) (hlen : bytes.size ≥ 10)
    (htype : bytes.get! 0 ≠ 1 ∧ bytes.get! 0 ≠ 2 ∧ bytes.get! 0 ≠ 3) :
    decodeMessage bytes = none := by
  unfold decodeMessage
  have hnot : ¬(bytes.size < 10) := by omega
  simp only [hnot, ↓reduceIte]
  rcases htype with ⟨h1, h2, h3⟩
  split <;> rename_i heq
  · exact False.elim (h1 heq)
  · exact False.elim (h2 heq)
  · exact False.elim (h3 heq)
  · rfl

/-! ### Wire Round-Trip Inversion Property -/

/-- Inversion predicate: A message satisfies round-trip wire serialization
    if decoding the encoded byte array yields exactly `some msg`. -/
def SatisfiesWireRoundTrip (msg : Message) : Prop :=
  decodeMessage (encodeMessage msg) = some msg

/-! ### Edge Cases: Empty Gossip Updates -/

/-- Round-trip inversion for ping with empty gossip updates. -/
theorem roundtrip_ping_empty :
    decodeMessage (encodeMessage (.ping 100 42 #[])) = some (.ping 100 42 #[]) := by
  unfold encodeMessage decodeMessage pushGossipUpdates pushGossipUpdates.loop decodeGossipUpdates decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for ack with empty gossip updates. -/
theorem roundtrip_ack_empty :
    decodeMessage (encodeMessage (.ack 100 42 #[])) = some (.ack 100 42 #[]) := by
  unfold encodeMessage decodeMessage pushGossipUpdates pushGossipUpdates.loop decodeGossipUpdates decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for pingReq with empty gossip updates. -/
theorem roundtrip_pingReq_empty :
    decodeMessage (encodeMessage (.pingReq 100 200 42 #[])) = some (.pingReq 100 200 42 #[]) := by
  unfold encodeMessage decodeMessage pushGossipUpdates pushGossipUpdates.loop decodeGossipUpdates decodeGossipUpdates.loop
  rfl

/-! ### Edge Cases: Single Gossip Update (All MemberStatus Variants) -/

/-- Round-trip inversion for ping with a single `alive` gossip update. -/
theorem roundtrip_ping_single_alive :
    let u : GossipUpdate := { id := 1, status := .alive, incarnation := 10, transmissions := 2 }
    decodeMessage (encodeMessage (.ping 100 42 #[u])) = some (.ping 100 42 #[u]) := by
  intro u
  unfold u encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for ping with a single `suspect` gossip update. -/
theorem roundtrip_ping_single_suspect :
    let u : GossipUpdate := { id := 2, status := .suspect, incarnation := 15, transmissions := 1 }
    decodeMessage (encodeMessage (.ping 100 42 #[u])) = some (.ping 100 42 #[u]) := by
  intro u
  unfold u encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for ping with a single `dead` gossip update. -/
theorem roundtrip_ping_single_dead :
    let u : GossipUpdate := { id := 3, status := .dead, incarnation := 20, transmissions := 0 }
    decodeMessage (encodeMessage (.ping 100 42 #[u])) = some (.ping 100 42 #[u]) := by
  intro u
  unfold u encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for ack with a single `alive` gossip update. -/
theorem roundtrip_ack_single_alive :
    let u : GossipUpdate := { id := 1, status := .alive, incarnation := 10, transmissions := 2 }
    decodeMessage (encodeMessage (.ack 100 42 #[u])) = some (.ack 100 42 #[u]) := by
  intro u
  unfold u encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for ack with a single `suspect` gossip update. -/
theorem roundtrip_ack_single_suspect :
    let u : GossipUpdate := { id := 2, status := .suspect, incarnation := 15, transmissions := 1 }
    decodeMessage (encodeMessage (.ack 100 42 #[u])) = some (.ack 100 42 #[u]) := by
  intro u
  unfold u encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for ack with a single `dead` gossip update. -/
theorem roundtrip_ack_single_dead :
    let u : GossipUpdate := { id := 3, status := .dead, incarnation := 20, transmissions := 0 }
    decodeMessage (encodeMessage (.ack 100 42 #[u])) = some (.ack 100 42 #[u]) := by
  intro u
  unfold u encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for pingReq with a single `alive` gossip update. -/
theorem roundtrip_pingReq_single_alive :
    let u : GossipUpdate := { id := 1, status := .alive, incarnation := 10, transmissions := 2 }
    decodeMessage (encodeMessage (.pingReq 100 200 42 #[u])) = some (.pingReq 100 200 42 #[u]) := by
  intro u
  unfold u encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for pingReq with a single `suspect` gossip update. -/
theorem roundtrip_pingReq_single_suspect :
    let u : GossipUpdate := { id := 2, status := .suspect, incarnation := 15, transmissions := 1 }
    decodeMessage (encodeMessage (.pingReq 100 200 42 #[u])) = some (.pingReq 100 200 42 #[u]) := by
  intro u
  unfold u encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for pingReq with a single `dead` gossip update. -/
theorem roundtrip_pingReq_single_dead :
    let u : GossipUpdate := { id := 3, status := .dead, incarnation := 20, transmissions := 0 }
    decodeMessage (encodeMessage (.pingReq 100 200 42 #[u])) = some (.pingReq 100 200 42 #[u]) := by
  intro u
  unfold u encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-! ### Edge Cases: Multiple Gossip Updates (2 and 3 Updates) -/

/-- Round-trip inversion for ping with 2 updates (heterogeneous status and incarnations). -/
theorem roundtrip_ping_multi_2 :
    let u1 : GossipUpdate := { id := 10, status := .alive, incarnation := 1, transmissions := 2 }
    let u2 : GossipUpdate := { id := 20, status := .suspect, incarnation := 3, transmissions := 0 }
    decodeMessage (encodeMessage (.ping 100 42 #[u1, u2])) = some (.ping 100 42 #[u1, u2]) := by
  intro u1 u2
  unfold u1 u2 encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for ack with 2 updates. -/
theorem roundtrip_ack_multi_2 :
    let u1 : GossipUpdate := { id := 10, status := .alive, incarnation := 1, transmissions := 2 }
    let u2 : GossipUpdate := { id := 20, status := .suspect, incarnation := 3, transmissions := 0 }
    decodeMessage (encodeMessage (.ack 100 42 #[u1, u2])) = some (.ack 100 42 #[u1, u2]) := by
  intro u1 u2
  unfold u1 u2 encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for pingReq with 2 updates. -/
theorem roundtrip_pingReq_multi_2 :
    let u1 : GossipUpdate := { id := 10, status := .alive, incarnation := 1, transmissions := 2 }
    let u2 : GossipUpdate := { id := 20, status := .suspect, incarnation := 3, transmissions := 0 }
    decodeMessage (encodeMessage (.pingReq 100 200 42 #[u1, u2])) = some (.pingReq 100 200 42 #[u1, u2]) := by
  intro u1 u2
  unfold u1 u2 encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for ping with 3 updates (covering all 3 MemberStatus constructors simultaneously). -/
theorem roundtrip_ping_multi_3 :
    let u1 : GossipUpdate := { id := 1, status := .alive, incarnation := 10, transmissions := 0 }
    let u2 : GossipUpdate := { id := 2, status := .suspect, incarnation := 11, transmissions := 1 }
    let u3 : GossipUpdate := { id := 3, status := .dead, incarnation := 12, transmissions := 2 }
    decodeMessage (encodeMessage (.ping 50 99 #[u1, u2, u3])) = some (.ping 50 99 #[u1, u2, u3]) := by
  intro u1 u2 u3
  unfold u1 u2 u3 encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for ack with 3 updates. -/
theorem roundtrip_ack_multi_3 :
    let u1 : GossipUpdate := { id := 1, status := .alive, incarnation := 10, transmissions := 0 }
    let u2 : GossipUpdate := { id := 2, status := .suspect, incarnation := 11, transmissions := 1 }
    let u3 : GossipUpdate := { id := 3, status := .dead, incarnation := 12, transmissions := 2 }
    decodeMessage (encodeMessage (.ack 50 99 #[u1, u2, u3])) = some (.ack 50 99 #[u1, u2, u3]) := by
  intro u1 u2 u3
  unfold u1 u2 u3 encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip inversion for pingReq with 3 updates. -/
theorem roundtrip_pingReq_multi_3 :
    let u1 : GossipUpdate := { id := 1, status := .alive, incarnation := 10, transmissions := 0 }
    let u2 : GossipUpdate := { id := 2, status := .suspect, incarnation := 11, transmissions := 1 }
    let u3 : GossipUpdate := { id := 3, status := .dead, incarnation := 12, transmissions := 2 }
    decodeMessage (encodeMessage (.pingReq 50 75 99 #[u1, u2, u3])) = some (.pingReq 50 75 99 #[u1, u2, u3]) := by
  intro u1 u2 u3
  unfold u1 u2 u3 encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-! ### Boundary Cases: Extreme Integer Ranges -/

/-- Round-trip preservation when all numeric fields are zero. -/
theorem roundtrip_ping_zero_fields :
    let u0 : GossipUpdate := { id := 0, status := .alive, incarnation := 0, transmissions := 0 }
    let msg : Message := .ping 0 0 #[u0]
    decodeMessage (encodeMessage msg) = some msg := by
  intro u0 msg
  unfold msg u0 encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip preservation for ack with all fields zero. -/
theorem roundtrip_ack_zero_fields :
    let u0 : GossipUpdate := { id := 0, status := .alive, incarnation := 0, transmissions := 0 }
    let msg : Message := .ack 0 0 #[u0]
    decodeMessage (encodeMessage msg) = some msg := by
  intro u0 msg
  unfold msg u0 encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip preservation for pingReq with all fields zero. -/
theorem roundtrip_pingReq_zero_fields :
    let u0 : GossipUpdate := { id := 0, status := .alive, incarnation := 0, transmissions := 0 }
    let msg : Message := .pingReq 0 0 0 #[u0]
    decodeMessage (encodeMessage msg) = some msg := by
  intro u0 msg
  unfold msg u0 encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip preservation when all numeric fields are maximum possible UInt32 / UInt8 values. -/
theorem roundtrip_ping_max_fields :
    let maxU32 : UInt32 := 4294967295
    let maxU8 : UInt8 := 255
    let uMax : GossipUpdate := { id := maxU32, status := .dead, incarnation := maxU32, transmissions := maxU8 }
    let msg : Message := .ping maxU32 maxU32 #[uMax]
    decodeMessage (encodeMessage msg) = some msg := by
  intro maxU32 maxU8 uMax msg
  unfold msg uMax maxU32 maxU8 encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip preservation for ack with maximum UInt32 / UInt8 values. -/
theorem roundtrip_ack_max_fields :
    let maxU32 : UInt32 := 4294967295
    let maxU8 : UInt8 := 255
    let uMax : GossipUpdate := { id := maxU32, status := .dead, incarnation := maxU32, transmissions := maxU8 }
    let msg : Message := .ack maxU32 maxU32 #[uMax]
    decodeMessage (encodeMessage msg) = some msg := by
  intro maxU32 maxU8 uMax msg
  unfold msg uMax maxU32 maxU8 encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-- Round-trip preservation for pingReq with maximum UInt32 / UInt8 values on all endpoints. -/
theorem roundtrip_pingReq_max_fields :
    let maxU32 : UInt32 := 4294967295
    let maxU8 : UInt8 := 255
    let uMax : GossipUpdate := { id := maxU32, status := .dead, incarnation := maxU32, transmissions := maxU8 }
    let msg : Message := .pingReq maxU32 maxU32 maxU32 #[uMax]
    decodeMessage (encodeMessage msg) = some msg := by
  intro maxU32 maxU8 uMax msg
  unfold msg uMax maxU32 maxU8 encodeMessage decodeMessage
  unfold pushGossipUpdates pushGossipUpdates.loop pushGossipUpdates.loop
  unfold decodeGossipUpdates decodeGossipUpdates.loop decodeGossipUpdates.loop
  rfl

/-! ### Universal Quantified Round-Trip Bijection Theorem -/

private theorem byteArray_get!_eq (b : ByteArray) (i : Nat) : b.get! i = b[i]! := by
  by_cases h : i < b.size
  · have h1 : b.get! i = b.data[i]! := by cases b; rfl
    have h2 : b[i]! = b.data[i] := by
      rw [getElem!_pos b i h]
      exact ByteArray.getElem_eq_getElem_data
    have h3 : b.data[i]! = b.data[i] := getElem!_pos b.data i h
    rw [h1, h2, h3]
  · have h1 : b.get! i = b.data[i]! := by cases b; rfl
    have h2 : b[i]! = default := getElem!_neg b i h
    have h3 : b.data[i]! = default := getElem!_neg b.data i h
    rw [h1, h2, h3]

private theorem byteArray_get!_push_lt (b : ByteArray) (x : UInt8) (i : Nat) (hi : i < b.size) :
    (b.push x).get! i = b.get! i := by
  simp only [byteArray_get!_eq]
  exact ByteArray.getElem!_push_lt b x i hi

private theorem byteArray_get!_push_eq (b : ByteArray) (x : UInt8) :
    (b.push x).get! b.size = x := by
  simp only [byteArray_get!_eq]
  exact ByteArray.getElem!_push_eq b x

/-- `PrefixOf b1 b2` holds when `b2` extends `b1` without mutating any byte `< b1.size`. -/
def PrefixOf (b1 b2 : ByteArray) : Prop :=
  b1.size ≤ b2.size ∧ ∀ i, i < b1.size → b2.get! i = b1.get! i

theorem PrefixOf_refl (b : ByteArray) : PrefixOf b b :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem PrefixOf_trans {a b c : ByteArray} (hab : PrefixOf a b) (hbc : PrefixOf b c) : PrefixOf a c :=
  ⟨Nat.le_trans hab.1 hbc.1, fun i hi => by
    rw [hbc.2 i (Nat.lt_of_lt_of_le hi hab.1), hab.2 i hi]⟩

theorem PrefixOf_get! {b1 b2 : ByteArray} (h : PrefixOf b1 b2) {i : Nat} (hi : i < b1.size) :
    b2.get! i = b1.get! i :=
  h.2 i hi

theorem PrefixOf_push (b : ByteArray) (x : UInt8) : PrefixOf b (b.push x) :=
  ⟨by rw [ByteArray.size_push]; omega, fun i hi => byteArray_get!_push_lt b x i hi⟩

theorem PrefixOf_pushUInt32BE (b : ByteArray) (v : UInt32) : PrefixOf b (pushUInt32BE b v) := by
  unfold pushUInt32BE
  exact PrefixOf_trans (PrefixOf_push _ _) <|
        PrefixOf_trans (PrefixOf_push _ _) <|
        PrefixOf_trans (PrefixOf_push _ _) (PrefixOf_push _ _)

theorem PrefixOf_pushGossipUpdate (b : ByteArray) (u : GossipUpdate) :
    PrefixOf b (pushGossipUpdate b u) := by
  unfold pushGossipUpdate
  exact PrefixOf_trans (PrefixOf_pushUInt32BE _ _) <|
        PrefixOf_trans (PrefixOf_push _ _) <|
        PrefixOf_trans (PrefixOf_pushUInt32BE _ _) (PrefixOf_push _ _)

theorem PrefixOf_pushGossipUpdates_loop (updates : Array GossipUpdate) (count i : Nat) (acc : ByteArray) :
    PrefixOf acc (pushGossipUpdates.loop updates count i acc) := by
  induction i, acc using pushGossipUpdates.loop.induct updates count with
  | case1 i acc h u ih =>
    rw [pushGossipUpdates.loop.eq_def]
    simp only [h, ↓reduceDIte]
    exact PrefixOf_trans (PrefixOf_pushGossipUpdate acc _) ih
  | case2 i acc h =>
    rw [pushGossipUpdates.loop.eq_def]
    simp only [h, ↓reduceDIte]
    exact PrefixOf_refl acc

theorem PrefixOf_pushGossipUpdates (b : ByteArray) (updates : Array GossipUpdate) (count : Nat) :
    PrefixOf b (pushGossipUpdates b updates count) :=
  PrefixOf_pushGossipUpdates_loop updates count 0 b

theorem uint32_toUInt8_recombine (v : UInt32) :
    ((((v >>> 24).toUInt8.toUInt32) <<< 24) |||
     (((v >>> 16).toUInt8.toUInt32) <<< 16) |||
     (((v >>> 8).toUInt8.toUInt32) <<< 8) |||
     (v.toUInt8.toUInt32)) = v := by
  bv_decide

theorem readUInt32BE_pushUInt32BE (b bytes : ByteArray) (v : UInt32)
    (hpre : PrefixOf (pushUInt32BE b v) bytes) :
    readUInt32BE bytes b.size = some v := by
  have hsz_push : (pushUInt32BE b v).size = b.size + 4 := pushUInt32BE_size b v
  have hsz : b.size + 4 ≤ bytes.size := by rw [← hsz_push]; exact hpre.1
  unfold readUInt32BE
  simp only [hsz, ↓reduceIte]
  have hb0 : bytes.get! b.size = (v >>> 24).toUInt8 := by
    rw [hpre.2 b.size (by rw [hsz_push]; omega)]
    have hp : PrefixOf (b.push (v >>> 24).toUInt8) (pushUInt32BE b v) := by
      unfold pushUInt32BE
      exact PrefixOf_trans (PrefixOf_push _ _) <| PrefixOf_trans (PrefixOf_push _ _) (PrefixOf_push _ _)
    rw [PrefixOf_get! hp (by simp [ByteArray.size_push])]
    exact byteArray_get!_push_eq b _
  have hb1 : bytes.get! (b.size + 1) = (v >>> 16).toUInt8 := by
    rw [hpre.2 (b.size + 1) (by rw [hsz_push]; omega)]
    have hp : PrefixOf ((b.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8) (pushUInt32BE b v) := by
      unfold pushUInt32BE
      exact PrefixOf_trans (PrefixOf_push _ _) (PrefixOf_push _ _)
    rw [PrefixOf_get! hp (by simp [ByteArray.size_push])]
    have hlt : b.size + 1 = (b.push (v >>> 24).toUInt8).size := by simp [ByteArray.size_push]
    rw [hlt]
    exact byteArray_get!_push_eq _ _
  have hb2 : bytes.get! (b.size + 2) = (v >>> 8).toUInt8 := by
    rw [hpre.2 (b.size + 2) (by rw [hsz_push]; omega)]
    have hp : PrefixOf (((b.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8) (pushUInt32BE b v) := by
      unfold pushUInt32BE
      exact PrefixOf_push _ _
    rw [PrefixOf_get! hp (by simp [ByteArray.size_push])]
    have hlt : b.size + 2 = ((b.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).size := by
      simp [ByteArray.size_push]
    rw [hlt]
    exact byteArray_get!_push_eq _ _
  have hb3 : bytes.get! (b.size + 3) = v.toUInt8 := by
    rw [hpre.2 (b.size + 3) (by rw [hsz_push]; omega)]
    unfold pushUInt32BE
    have hlt : b.size + 3 = (((b.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8).size := by
      simp [ByteArray.size_push]
    rw [hlt]
    exact byteArray_get!_push_eq _ _
  rw [hb0, hb1, hb2, hb3]
  exact congrArg some (uint32_toUInt8_recombine v)

theorem readGossipUpdate_pushGossipUpdate (b bytes : ByteArray) (u : GossipUpdate)
    (hpre : PrefixOf (pushGossipUpdate b u) bytes) :
    readGossipUpdate bytes b.size = some (u, b.size + 10) := by
  have hsz_push : (pushGossipUpdate b u).size = b.size + 10 := pushGossipUpdate_size b u
  have hsz : b.size + 10 ≤ bytes.size := by rw [← hsz_push]; exact hpre.1
  unfold readGossipUpdate
  simp only [hsz, ↓reduceIte]
  have hid : readUInt32BE bytes b.size = some u.id := by
    apply readUInt32BE_pushUInt32BE b bytes u.id
    have h1 : PrefixOf (pushUInt32BE b u.id) (pushGossipUpdate b u) := by
      unfold pushGossipUpdate
      exact PrefixOf_trans (PrefixOf_push _ _) <|
            PrefixOf_trans (PrefixOf_pushUInt32BE _ _) (PrefixOf_push _ _)
    exact PrefixOf_trans h1 hpre
  have hst : bytes.get! (b.size + 4) = encodeMemberStatus u.status := by
    rw [hpre.2 (b.size + 4) (by rw [hsz_push]; omega)]
    have hp : PrefixOf ((pushUInt32BE b u.id).push (encodeMemberStatus u.status)) (pushGossipUpdate b u) := by
      unfold pushGossipUpdate
      exact PrefixOf_trans (PrefixOf_pushUInt32BE _ _) (PrefixOf_push _ _)
    rw [PrefixOf_get! hp (by simp [ByteArray.size_push, pushUInt32BE_size])]
    have hlt : b.size + 4 = (pushUInt32BE b u.id).size := (pushUInt32BE_size b u.id).symm
    rw [hlt]
    exact byteArray_get!_push_eq _ _
  have hinc : readUInt32BE bytes (b.size + 5) = some u.incarnation := by
    have hpos : b.size + 5 = ((pushUInt32BE b u.id).push (encodeMemberStatus u.status)).size := by
      simp [ByteArray.size_push, pushUInt32BE_size]
    rw [hpos]
    apply readUInt32BE_pushUInt32BE _ bytes u.incarnation
    have h1 : PrefixOf (pushUInt32BE ((pushUInt32BE b u.id).push (encodeMemberStatus u.status)) u.incarnation) (pushGossipUpdate b u) := by
      unfold pushGossipUpdate
      exact PrefixOf_push _ _
    exact PrefixOf_trans h1 hpre
  have htx : bytes.get! (b.size + 9) = u.transmissions := by
    rw [hpre.2 (b.size + 9) (by rw [hsz_push]; omega)]
    unfold pushGossipUpdate
    have hlt : b.size + 9 = (pushUInt32BE ((pushUInt32BE b u.id).push (encodeMemberStatus u.status)) u.incarnation).size := by
      simp [ByteArray.size_push, pushUInt32BE_size]
    rw [hlt]
    exact byteArray_get!_push_eq _ _
  rw [hid, hst, decodeMemberStatus_encodeMemberStatus, hinc, htx]

theorem decodeGossipUpdates_loop_eq (updates : Array GossipUpdate) (count i : Nat)
    (b bytes : ByteArray) (accOut : Array GossipUpdate)
    (hi : i ≤ count) (hcnt : count ≤ updates.size)
    (hacc : accOut.toList = updates.toList.take i)
    (hpre : PrefixOf (pushGossipUpdates.loop updates count i b) bytes) :
    decodeGossipUpdates.loop bytes count i b.size accOut =
      some (updates.extract 0 count) := by
  induction i, b using pushGossipUpdates.loop.induct updates count generalizing accOut with
  | case1 i b hlt u ih =>
    rw [decodeGossipUpdates.loop.eq_def]
    simp only [hlt, ↓reduceDIte]
    have hlt' : i < count := hlt
    have hle : i < updates.size := Nat.lt_of_lt_of_le hlt' hcnt
    have hu : u = updates[i] := by simp only [u, hle, ↓reduceDIte]
    have hpre_next : PrefixOf (pushGossipUpdates.loop updates count (i + 1) (pushGossipUpdate b u)) bytes := by
      rw [pushGossipUpdates.loop.eq_def] at hpre
      simpa [hlt] using hpre
    have hpre_step : PrefixOf (pushGossipUpdate b u) bytes :=
      PrefixOf_trans (PrefixOf_pushGossipUpdates_loop updates count (i + 1) (pushGossipUpdate b u)) hpre_next
    rw [readGossipUpdate_pushGossipUpdate b bytes u hpre_step]
    have hsz : (pushGossipUpdate b u).size = b.size + 10 := pushGossipUpdate_size b u
    rw [← hsz]
    refine ih (accOut.push u) (by omega) ?_ hpre_next
    rw [Array.toList_push, hacc, hu, List.take_add_one]
    simp [hle]
  | case2 i b hge =>
    rw [decodeGossipUpdates.loop.eq_def]
    simp only [hge, ↓reduceDIte]
    have hieq : i = count := by omega
    subst hieq
    congr 1
    apply Array.ext'
    rw [hacc, Array.toList_extract]
    simp

theorem decodeGossipUpdates_pushGossipUpdates (updates : Array GossipUpdate) (count : Nat)
    (b bytes : ByteArray) (hcnt : count ≤ updates.size)
    (hpre : PrefixOf (pushGossipUpdates b updates count) bytes) :
    decodeGossipUpdates bytes b.size count = some (updates.extract 0 count) := by
  unfold decodeGossipUpdates
  exact decodeGossipUpdates_loop_eq updates count 0 b bytes #[] (Nat.zero_le _) hcnt (by simp) hpre

/-- **Universal Wire Round-Trip Bijection Theorem**:
    For EVERY well-formed `Message` (up to 255 piggybacked gossip updates) with
    arbitrary 32-bit `NodeId`s, sequence numbers, incarnations, and statuses,
    encoding followed by decoding recovers the exact original message. -/
theorem decodeMessage_encodeMessage_wellFormed (msg : Message) (hwf : WellFormedMessage msg) :
    decodeMessage (encodeMessage msg) = some msg := by
  cases msg with
  | ping src seq updates =>
    have hcnt : updates.size ≤ 255 := hwf
    have hnot : ¬ (updates.size > 255) := by omega
    have hsz : (encodeMessage (.ping src seq updates)).size = 10 + updates.size * 10 :=
      encodeMessage_size_ping_wellFormed src seq updates hcnt
    let b0 := ByteArray.empty.push 1
    let b1 := pushUInt32BE b0 src
    let b2 := pushUInt32BE b1 seq
    let b3 := b2.push (if updates.size > 255 then 255 else updates.size).toUInt8
    have hb3_sz : b3.size = 10 := by simp [b3, b2, b1, b0, ByteArray.size_push, pushUInt32BE_size]
    have henc_eq : encodeMessage (.ping src seq updates) = pushGossipUpdates b3 updates updates.size := by
      unfold encodeMessage; simp [hnot, b3, b2, b1, b0]
    have hpre_b3 : PrefixOf b3 (encodeMessage (.ping src seq updates)) := by
      rw [henc_eq]; exact PrefixOf_pushGossipUpdates _ _ _
    have htag : (encodeMessage (.ping src seq updates)).get! 0 = 1 := by
      rw [PrefixOf_get! hpre_b3 (by rw [hb3_sz]; omega)]
      have hp0 : PrefixOf b0 b3 := PrefixOf_trans (PrefixOf_pushUInt32BE _ _) <|
        PrefixOf_trans (PrefixOf_pushUInt32BE _ _) (PrefixOf_push _ _)
      rw [PrefixOf_get! hp0 (by simp [b0, ByteArray.size_push])]
      exact byteArray_get!_push_eq ByteArray.empty 1
    have hcount_byte : (encodeMessage (.ping src seq updates)).get! 9 = updates.size.toUInt8 := by
      rw [PrefixOf_get! hpre_b3 (by rw [hb3_sz]; omega)]
      have h9 : (9 : Nat) = b2.size := by simp [b2, b1, b0, ByteArray.size_push, pushUInt32BE_size]
      rw [h9]
      simp [b3, hnot, byteArray_get!_push_eq]
    have hcount_nat : (updates.size.toUInt8).toNat = updates.size := by
      simp only [Nat.toUInt8, UInt8.toNat]; exact Nat.mod_eq_of_lt (by omega)
    have hsrc : readUInt32BE (encodeMessage (.ping src seq updates)) 1 = some src := by
      have h1 : (1 : Nat) = b0.size := by simp [b0, ByteArray.size_push]
      rw [h1]
      exact readUInt32BE_pushUInt32BE b0 _ src (PrefixOf_trans (PrefixOf_trans (PrefixOf_pushUInt32BE _ _) (PrefixOf_push _ _)) hpre_b3)
    have hseq : readUInt32BE (encodeMessage (.ping src seq updates)) 5 = some seq := by
      have h5 : (5 : Nat) = b1.size := by simp [b1, b0, ByteArray.size_push, pushUInt32BE_size]
      rw [h5]
      exact readUInt32BE_pushUInt32BE b1 _ seq (PrefixOf_trans (PrefixOf_push _ _) hpre_b3)
    have hupds : decodeGossipUpdates (encodeMessage (.ping src seq updates)) 10 updates.size = some updates := by
      rw [← hb3_sz]
      have hdec := decodeGossipUpdates_pushGossipUpdates updates updates.size b3 (encodeMessage (.ping src seq updates)) (Nat.le_refl _) (by rw [← henc_eq]; exact PrefixOf_refl _)
      simpa using hdec
    unfold decodeMessage
    rw [hsz]
    split
    · omega
    · simp only [htag, hcount_byte, hcount_nat, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [hsrc, hseq, hupds]
      simp [Bind.bind, Option.bind]
  | ack src seq updates =>
    have hcnt : updates.size ≤ 255 := hwf
    have hnot : ¬ (updates.size > 255) := by omega
    have hsz : (encodeMessage (.ack src seq updates)).size = 10 + updates.size * 10 :=
      encodeMessage_size_ack_wellFormed src seq updates hcnt
    let b0 := ByteArray.empty.push 2
    let b1 := pushUInt32BE b0 src
    let b2 := pushUInt32BE b1 seq
    let b3 := b2.push (if updates.size > 255 then 255 else updates.size).toUInt8
    have hb3_sz : b3.size = 10 := by simp [b3, b2, b1, b0, ByteArray.size_push, pushUInt32BE_size]
    have henc_eq : encodeMessage (.ack src seq updates) = pushGossipUpdates b3 updates updates.size := by
      unfold encodeMessage; simp [hnot, b3, b2, b1, b0]
    have hpre_b3 : PrefixOf b3 (encodeMessage (.ack src seq updates)) := by
      rw [henc_eq]; exact PrefixOf_pushGossipUpdates _ _ _
    have htag : (encodeMessage (.ack src seq updates)).get! 0 = 2 := by
      rw [PrefixOf_get! hpre_b3 (by rw [hb3_sz]; omega)]
      have hp0 : PrefixOf b0 b3 := PrefixOf_trans (PrefixOf_pushUInt32BE _ _) <|
        PrefixOf_trans (PrefixOf_pushUInt32BE _ _) (PrefixOf_push _ _)
      rw [PrefixOf_get! hp0 (by simp [b0, ByteArray.size_push])]
      exact byteArray_get!_push_eq ByteArray.empty 2
    have hcount_byte : (encodeMessage (.ack src seq updates)).get! 9 = updates.size.toUInt8 := by
      rw [PrefixOf_get! hpre_b3 (by rw [hb3_sz]; omega)]
      have h9 : (9 : Nat) = b2.size := by simp [b2, b1, b0, ByteArray.size_push, pushUInt32BE_size]
      rw [h9]
      simp [b3, hnot, byteArray_get!_push_eq]
    have hcount_nat : (updates.size.toUInt8).toNat = updates.size := by
      simp only [Nat.toUInt8, UInt8.toNat]; exact Nat.mod_eq_of_lt (by omega)
    have hsrc : readUInt32BE (encodeMessage (.ack src seq updates)) 1 = some src := by
      have h1 : (1 : Nat) = b0.size := by simp [b0, ByteArray.size_push]
      rw [h1]
      exact readUInt32BE_pushUInt32BE b0 _ src (PrefixOf_trans (PrefixOf_trans (PrefixOf_pushUInt32BE _ _) (PrefixOf_push _ _)) hpre_b3)
    have hseq : readUInt32BE (encodeMessage (.ack src seq updates)) 5 = some seq := by
      have h5 : (5 : Nat) = b1.size := by simp [b1, b0, ByteArray.size_push, pushUInt32BE_size]
      rw [h5]
      exact readUInt32BE_pushUInt32BE b1 _ seq (PrefixOf_trans (PrefixOf_push _ _) hpre_b3)
    have hupds : decodeGossipUpdates (encodeMessage (.ack src seq updates)) 10 updates.size = some updates := by
      rw [← hb3_sz]
      have hdec := decodeGossipUpdates_pushGossipUpdates updates updates.size b3 (encodeMessage (.ack src seq updates)) (Nat.le_refl _) (by rw [← henc_eq]; exact PrefixOf_refl _)
      simpa using hdec
    unfold decodeMessage
    rw [hsz]
    split
    · omega
    · simp only [htag, hcount_byte, hcount_nat, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [hsrc, hseq, hupds]
      simp [Bind.bind, Option.bind]
  | pingReq src target seq updates =>
    have hcnt : updates.size ≤ 255 := hwf
    have hnot : ¬ (updates.size > 255) := by omega
    have hsz : (encodeMessage (.pingReq src target seq updates)).size = 14 + updates.size * 10 :=
      encodeMessage_size_pingReq_wellFormed src target seq updates hcnt
    let b0 := ByteArray.empty.push 3
    let b1 := pushUInt32BE b0 src
    let b2 := pushUInt32BE b1 seq
    let b3 := pushUInt32BE b2 target
    let b4 := b3.push (if updates.size > 255 then 255 else updates.size).toUInt8
    have hb4_sz : b4.size = 14 := by simp [b4, b3, b2, b1, b0, ByteArray.size_push, pushUInt32BE_size]
    have henc_eq : encodeMessage (.pingReq src target seq updates) = pushGossipUpdates b4 updates updates.size := by
      unfold encodeMessage; simp [hnot, b4, b3, b2, b1, b0]
    have hpre_b4 : PrefixOf b4 (encodeMessage (.pingReq src target seq updates)) := by
      rw [henc_eq]; exact PrefixOf_pushGossipUpdates _ _ _
    have htag : (encodeMessage (.pingReq src target seq updates)).get! 0 = 3 := by
      rw [PrefixOf_get! hpre_b4 (by rw [hb4_sz]; omega)]
      have hp0 : PrefixOf b0 b4 := PrefixOf_trans (PrefixOf_pushUInt32BE _ _) <|
        PrefixOf_trans (PrefixOf_pushUInt32BE _ _) <|
        PrefixOf_trans (PrefixOf_pushUInt32BE _ _) (PrefixOf_push _ _)
      rw [PrefixOf_get! hp0 (by simp [b0, ByteArray.size_push])]
      exact byteArray_get!_push_eq ByteArray.empty 3
    have hcount_byte : (encodeMessage (.pingReq src target seq updates)).get! 13 = updates.size.toUInt8 := by
      rw [PrefixOf_get! hpre_b4 (by rw [hb4_sz]; omega)]
      have h13 : (13 : Nat) = b3.size := by simp [b3, b2, b1, b0, ByteArray.size_push, pushUInt32BE_size]
      rw [h13]
      simp [b4, hnot, byteArray_get!_push_eq]
    have hcount_nat : (updates.size.toUInt8).toNat = updates.size := by
      simp only [Nat.toUInt8, UInt8.toNat]; exact Nat.mod_eq_of_lt (by omega)
    have hsrc : readUInt32BE (encodeMessage (.pingReq src target seq updates)) 1 = some src := by
      have h1 : (1 : Nat) = b0.size := by simp [b0, ByteArray.size_push]
      rw [h1]
      exact readUInt32BE_pushUInt32BE b0 _ src (PrefixOf_trans (PrefixOf_trans (PrefixOf_pushUInt32BE _ _) (PrefixOf_trans (PrefixOf_pushUInt32BE _ _) (PrefixOf_push _ _))) hpre_b4)
    have hseq : readUInt32BE (encodeMessage (.pingReq src target seq updates)) 5 = some seq := by
      have h5 : (5 : Nat) = b1.size := by simp [b1, b0, ByteArray.size_push, pushUInt32BE_size]
      rw [h5]
      exact readUInt32BE_pushUInt32BE b1 _ seq (PrefixOf_trans (PrefixOf_trans (PrefixOf_pushUInt32BE _ _) (PrefixOf_push _ _)) hpre_b4)
    have htarget : readUInt32BE (encodeMessage (.pingReq src target seq updates)) 9 = some target := by
      have h9 : (9 : Nat) = b2.size := by simp [b2, b1, b0, ByteArray.size_push, pushUInt32BE_size]
      rw [h9]
      exact readUInt32BE_pushUInt32BE b2 _ target (PrefixOf_trans (PrefixOf_push _ _) hpre_b4)
    have hupds : decodeGossipUpdates (encodeMessage (.pingReq src target seq updates)) 14 updates.size = some updates := by
      rw [← hb4_sz]
      have hdec := decodeGossipUpdates_pushGossipUpdates updates updates.size b4 (encodeMessage (.pingReq src target seq updates)) (Nat.le_refl _) (by rw [← henc_eq]; exact PrefixOf_refl _)
      simpa using hdec
    unfold decodeMessage
    rw [hsz]
    split
    · omega
    · simp only [htag, hcount_byte, hcount_nat, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      split
      · omega
      · rw [hsrc, hseq, htarget, hupds]
        simp [Bind.bind, Option.bind]

theorem wellFormedMessage_satisfies_roundtrip (msg : Message) (hwf : WellFormedMessage msg) :
    SatisfiesWireRoundTrip msg :=
  decodeMessage_encodeMessage_wellFormed msg hwf

end SwimProofs

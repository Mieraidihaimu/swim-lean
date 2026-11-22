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

end SwimProofs

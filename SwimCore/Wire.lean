import SwimCore.Types

namespace SwimCore

/-- Convert `MemberStatus` to wire byte: 0 = alive, 1 = suspect, 2 = dead -/
def encodeMemberStatus (status : MemberStatus) : UInt8 :=
  match status with
  | .alive   => 0
  | .suspect => 1
  | .dead    => 2

/-- Parse `MemberStatus` from wire byte -/
def decodeMemberStatus (b : UInt8) : Option MemberStatus :=
  match b with
  | 0 => some .alive
  | 1 => some .suspect
  | 2 => some .dead
  | _ => none

/-- Append a 32-bit integer in big-endian byte order to a `ByteArray` -/
def pushUInt32BE (b : ByteArray) (v : UInt32) : ByteArray :=
  let b := b.push ((v >>> 24).toUInt8)
  let b := b.push ((v >>> 16).toUInt8)
  let b := b.push ((v >>> 8).toUInt8)
  b.push (v.toUInt8)

/-- Read a 32-bit big-endian integer starting at offset `pos` -/
def readUInt32BE (b : ByteArray) (pos : Nat) : Option UInt32 :=
  if pos + 4 <= b.size then
    let b0 := (b.get! pos).toUInt32
    let b1 := (b.get! (pos + 1)).toUInt32
    let b2 := (b.get! (pos + 2)).toUInt32
    let b3 := (b.get! (pos + 3)).toUInt32
    some ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3)
  else
    none

/-- Append a `GossipUpdate` record (10 bytes) in wire format:
    - 4-byte id (UInt32 BE)
    - 1-byte status (0 = alive, 1 = suspect, 2 = dead)
    - 4-byte incarnation (UInt32 BE)
    - 1-byte transmissions (UInt8)
-/
def pushGossipUpdate (b : ByteArray) (u : GossipUpdate) : ByteArray :=
  let b := pushUInt32BE b u.id
  let b := b.push (encodeMemberStatus u.status)
  let b := pushUInt32BE b u.incarnation
  b.push u.transmissions

/-- Read a `GossipUpdate` record (10 bytes) at offset `pos` -/
def readGossipUpdate (b : ByteArray) (pos : Nat) : Option (GossipUpdate × Nat) :=
  if pos + 10 <= b.size then
    match readUInt32BE b pos, decodeMemberStatus (b.get! (pos + 4)), readUInt32BE b (pos + 5) with
    | some id, some status, some inc =>
      let transmissions := b.get! (pos + 9)
      some ({ id := id, status := status, incarnation := inc, transmissions := transmissions }, pos + 10)
    | _, _, _ => none
  else
    none

/-- Append up to `count` `GossipUpdate` records to a `ByteArray` -/
def pushGossipUpdates (b : ByteArray) (updates : Array GossipUpdate) (count : Nat) : ByteArray :=
  let rec loop (i : Nat) (acc : ByteArray) : ByteArray :=
    if _h : i < count then
      let u := if h : i < updates.size then updates[i] else default
      loop (i + 1) (pushGossipUpdate acc u)
    else
      acc
  termination_by count - i
  loop 0 b

/-- Decode `count` `GossipUpdate` records starting at `offset` -/
def decodeGossipUpdates (bytes : ByteArray) (offset : Nat) (count : Nat) : Option (Array GossipUpdate) :=
  let rec loop (i : Nat) (pos : Nat) (acc : Array GossipUpdate) : Option (Array GossipUpdate) :=
    if _h : i < count then
      match readGossipUpdate bytes pos with
      | some (u, nextPos) => loop (i + 1) nextPos (acc.push u)
      | none => none
    else
      some acc
  termination_by count - i
  loop 0 offset #[]

/-- Encode a `Message` into a raw `ByteArray` using compact big-endian wire format:
    - Byte 0: MsgType (1 = Ping, 2 = Ack, 3 = PingReq)
    - Bytes 1-4: src NodeId (UInt32)
    - Bytes 5-8: seq (UInt32)
    - (If PingReq: Bytes 9-12 target NodeId)
    - Updates section: 1-byte count N, followed by records (10 bytes each)
-/
def encodeMessage (msg : Message) : ByteArray :=
  let (msgType, src, seq, maybeTarget, updates) :=
    match msg with
    | .ping src seq updates => ((1 : UInt8), src, seq, none, updates)
    | .ack src seq updates => ((2 : UInt8), src, seq, none, updates)
    | .pingReq src target seq updates => ((3 : UInt8), src, seq, some target, updates)
  let count := if updates.size > 255 then 255 else updates.size
  let b := ByteArray.empty
  let b := b.push msgType
  let b := pushUInt32BE b src
  let b := pushUInt32BE b seq
  let b := match maybeTarget with
    | some target => pushUInt32BE b target
    | none => b
  let b := b.push count.toUInt8
  pushGossipUpdates b updates count

/-- Decode a `Message` from raw `ByteArray` using compact big-endian wire format -/
def decodeMessage (bytes : ByteArray) : Option Message := do
  if bytes.size < 10 then
    none
  else
    let msgType := bytes.get! 0
    match msgType with
    | 1 => -- Ping
      let count := (bytes.get! 9).toNat
      if bytes.size != 10 + count * 10 then
        none
      else
        let src ← readUInt32BE bytes 1
        let seq ← readUInt32BE bytes 5
        let updates ← decodeGossipUpdates bytes 10 count
        some (.ping src seq updates)
    | 2 => -- Ack
      let count := (bytes.get! 9).toNat
      if bytes.size != 10 + count * 10 then
        none
      else
        let src ← readUInt32BE bytes 1
        let seq ← readUInt32BE bytes 5
        let updates ← decodeGossipUpdates bytes 10 count
        some (.ack src seq updates)
    | 3 => -- PingReq
      if bytes.size < 14 then
        none
      else
        let count := (bytes.get! 13).toNat
        if bytes.size != 14 + count * 10 then
          none
        else
          let src ← readUInt32BE bytes 1
          let seq ← readUInt32BE bytes 5
          let target ← readUInt32BE bytes 9
          let updates ← decodeGossipUpdates bytes 14 count
          some (.pingReq src target seq updates)
    | _ => none

end SwimCore

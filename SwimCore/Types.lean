namespace SwimCore

/-- Node identifier as dense 32-bit integer -/
abbrev NodeId := UInt32

/-- Incarnation number for overriding stale suspicion/alive states -/
abbrev Incarnation := UInt32

/-- Protocol timestamp in monotonic milliseconds -/
abbrev Timestamp := UInt64

/-- Peer IPv4 address and port -/
structure PeerAddr where
  ip   : UInt32
  port : UInt16
deriving Inhabited, BEq, Repr

/-- Membership status of a node in the SWIM protocol -/
inductive MemberStatus where
  | alive
  | suspect
  | dead
deriving Inhabited, BEq, Repr

/-- Full membership record for a known cluster peer -/
structure MemberEntry where
  id              : NodeId
  addr            : PeerAddr
  status          : MemberStatus
  incarnation     : Incarnation
  suspectDeadline : Timestamp
deriving Inhabited, BEq, Repr

/-- Piggybacked gossip update disseminated across protocol periods -/
structure GossipUpdate where
  id            : NodeId
  status        : MemberStatus
  incarnation   : Incarnation
  transmissions : UInt8
deriving Inhabited, BEq, Repr

/-- Protocol message types transmitted over UDP -/
inductive Message where
  | ping (src : NodeId) (seq : UInt32) (updates : Array GossipUpdate)
  | ack (src : NodeId) (seq : UInt32) (updates : Array GossipUpdate)
  | pingReq (src : NodeId) (target : NodeId) (seq : UInt32) (updates : Array GossipUpdate)
deriving Inhabited, BEq, Repr

/-- External event driving the pure protocol state machine -/
inductive Event where
  | recvPacket (src : PeerAddr) (payload : ByteArray) (now : Timestamp)
  | tick (now : Timestamp)
deriving Inhabited

/-- Actions emitted by the pure protocol state machine to be executed by C shell -/
inductive Action where
  | sendPacket (dst : PeerAddr) (payload : ByteArray)
  | emitMembershipChange (node : NodeId) (status : MemberStatus) (incarnation : Incarnation)
deriving Inhabited

end SwimCore

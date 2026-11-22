import SwimCore.Types
import SwimCore.FailureDetector
import SwimCore.Wire

namespace SwimCore

/-- Initialize a SWIM node with a node ID, IP address (IPv4 as 32-bit big-endian integer),
    UDP port, and 64-bit PRNG seed. Initial cluster peer list is empty. -/
@[export swim_init_node]
def swimInitNode (id : UInt32) (ip : UInt32) (port : UInt16) (seed : UInt64) : NodeState :=
  initNode id { ip := ip, port := port } seed #[]

/-- Add a known peer node with its ID, IP address, and UDP port to the cluster membership. -/
@[export swim_add_peer]
def swimAddPeer (st : NodeState) (id : UInt32) (ip : UInt32) (port : UInt16) : NodeState :=
  addPeer st id { ip := ip, port := port }

/-- Process a periodic protocol timer tick event at monotonic timestamp `now` (in milliseconds).
    Returns a pair `(newState, actions)` containing the updated `NodeState` and an `Array Action`. -/
@[export swim_step_tick]
def swimStepTick (st : NodeState) (now : UInt64) : NodeState × Array Action :=
  step st (Event.tick now)

/-- Process an incoming network packet received from `srcIp:srcPort` with raw `payload` at
    monotonic timestamp `now` (in milliseconds).
    Returns a pair `(newState, actions)` containing the updated `NodeState` and an `Array Action`. -/
@[export swim_step_packet]
def swimStepPacket (st : NodeState) (srcIp : UInt32) (srcPort : UInt16) (payload : ByteArray) (now : UInt64) : NodeState × Array Action :=
  step st (Event.recvPacket { ip := srcIp, port := srcPort } payload now)

/-- Extract the new `NodeState` from a step result pair `(NodeState × Array Action)`. -/
@[export swim_step_result_state]
def swimStepResultState (res : NodeState × Array Action) : NodeState :=
  res.1

/-- Extract the `Array Action` from a step result pair `(NodeState × Array Action)`. -/
@[export swim_step_result_actions]
def swimStepResultActions (res : NodeState × Array Action) : Array Action :=
  res.2

/-- Get the number of actions in an `Array Action`. -/
@[export swim_actions_size]
def swimActionsSize (actions : Array Action) : UInt32 :=
  actions.size.toUInt32

/-- Get an action at index `idx` from an `Array Action`. Returns dummy send action if out of bounds. -/
@[export swim_actions_get]
def swimActionsGet (actions : Array Action) (idx : UInt32) : Action :=
  if h : idx.toNat < actions.size then
    actions[idx.toNat]
  else
    Action.sendPacket { ip := 0, port := 0 } ByteArray.empty

/-- Check if an action is a `sendPacket` action. -/
@[export swim_action_is_send]
def swimActionIsSend (act : Action) : Bool :=
  match act with
  | Action.sendPacket _ _ => true
  | _ => false

/-- Extract destination IP address from a `sendPacket` action. Returns 0 if not a sendPacket action. -/
@[export swim_action_send_dest_ip]
def swimActionSendDestIp (act : Action) : UInt32 :=
  match act with
  | Action.sendPacket dst _ => dst.ip
  | _ => 0

/-- Extract destination UDP port from a `sendPacket` action. Returns 0 if not a sendPacket action. -/
@[export swim_action_send_dest_port]
def swimActionSendDestPort (act : Action) : UInt16 :=
  match act with
  | Action.sendPacket dst _ => dst.port
  | _ => 0

/-- Extract packet payload ByteArray from a `sendPacket` action. Returns empty ByteArray if not a sendPacket action. -/
@[export swim_action_send_payload]
def swimActionSendPayload (act : Action) : ByteArray :=
  match act with
  | Action.sendPacket _ payload => payload
  | _ => ByteArray.empty

/-- Check if an action is an `emitMembershipChange` action. -/
@[export swim_action_is_membership_change]
def swimActionIsMembershipChange (act : Action) : Bool :=
  match act with
  | Action.emitMembershipChange _ _ _ => true
  | _ => false

/-- Extract member NodeId from an `emitMembershipChange` action. Returns 0 if not a membership change action. -/
@[export swim_action_membership_node]
def swimActionMembershipNode (act : Action) : UInt32 :=
  match act with
  | Action.emitMembershipChange node _ _ => node
  | _ => 0

/-- Extract status from an `emitMembershipChange` action (0 = alive, 1 = suspect, 2 = dead).
    Returns 255 if not a membership change action. -/
@[export swim_action_membership_status]
def swimActionMembershipStatus (act : Action) : UInt8 :=
  match act with
  | Action.emitMembershipChange _ status _ =>
    match status with
    | MemberStatus.alive   => 0
    | MemberStatus.suspect => 1
    | MemberStatus.dead    => 2
  | _ => 255

/-- Extract incarnation from an `emitMembershipChange` action. Returns 0 if not a membership change action. -/
@[export swim_action_membership_incarnation]
def swimActionMembershipIncarnation (act : Action) : UInt32 :=
  match act with
  | Action.emitMembershipChange _ _ inc => inc
  | _ => 0

end SwimCore

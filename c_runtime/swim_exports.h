#ifndef SWIM_EXPORTS_H
#define SWIM_EXPORTS_H

#include <stdint.h>
#include <stdbool.h>
#include <lean/lean.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Lean 4 Runtime Initialization */
void lean_initialize_runtime_module(void);

/* SwimCore Module Initializer */
lean_object* initialize_swim_SwimCore(uint8_t builtin);

/* Node initialization */
lean_object* swim_init_node(uint32_t id, uint32_t ip, uint16_t port, uint64_t seed);
lean_object* swim_add_peer(lean_object* st, uint32_t id, uint32_t ip, uint16_t port);

/* Step transitions */
lean_object* swim_step_tick(lean_object* st, uint64_t now);
lean_object* swim_step_packet(lean_object* st, uint32_t srcIp, uint16_t srcPort, lean_object* payload, uint64_t now);

/* Step result decomposition helpers (borrowed @& arguments) */
lean_object* swim_step_result_state(lean_object* res);
lean_object* swim_step_result_actions(lean_object* res);
uint64_t     swim_next_wakeup_at(lean_object* st);

/* Read-only state observation helpers */
uint32_t     swim_self_incarnation(lean_object* st);
uint32_t     swim_members_size(lean_object* st);
uint8_t      swim_member_status(lean_object* st, uint32_t id);

/* Array Action accessors */
uint32_t     swim_actions_size(lean_object* actions);
lean_object* swim_actions_get(lean_object* actions, uint32_t idx);

/* Action inspection helpers */
uint8_t      swim_action_is_send(lean_object* act);
uint32_t     swim_action_send_dest_ip(lean_object* act);
uint16_t     swim_action_send_dest_port(lean_object* act);
lean_object* swim_action_send_payload(lean_object* act);

/* Membership change inspection helpers */
uint8_t      swim_action_is_membership_change(lean_object* act);
uint32_t     swim_action_membership_node(lean_object* act);
uint8_t      swim_action_membership_status(lean_object* act);
uint32_t     swim_action_membership_incarnation(lean_object* act);

#ifdef __cplusplus
}
#endif

#endif /* SWIM_EXPORTS_H */

import SwimCore.Types
import SwimCore.FailureDetector
import SwimProofs.Safety

/-!
# State-Machine Safety Refinement Proofs

This module formally bridges the executable state machine `SwimCore.FailureDetector`
with the mathematical join-semilattice invariants in `SwimProofs.Safety`.

Specifically, we prove:
1. `shouldOverride` is equivalent to strict dominance in `Dominates`.
2. `markSuspect` preserves `StateMonotonic` (local incarnation never decreases,
   membership size is invariant, and every member entry dominates its prior state).
3. `checkSuspectTimeouts` preserves `StateMonotonic` across the entire membership table.
4. `mergeGossipUpdates` preserves `StateMonotonic` (including saturating self-refutation).
5. **Master Transition Safety Theorem (`step_preserves_safety`)**: For every
   `Event` (`tick` or `recvPacket`), `SwimCore.step` preserves `StateMonotonic`.
-/

namespace SwimProofs

open SwimCore

/-! ### Bridging `shouldOverride` and `Dominates` -/

theorem uint32_gt_to_lt {a b : UInt32} (h : (a > b) = true) : b < a := by
  simpa using h

theorem uint32_beq_eq {a b : UInt32} (h : (a == b) = true) : a = b := by
  simpa using h

/-- Whenever `shouldOverride newInc newSt curInc curSt = true`, the incoming observation
    strictly dominates (hence dominates) the current observation in the `Dominates` lattice. -/
theorem shouldOverride_implies_dominates (newInc : Incarnation) (newSt : MemberStatus)
    (curInc : Incarnation) (curSt : MemberStatus)
    (h : shouldOverride newInc newSt curInc curSt = true) :
    Dominates newInc newSt curInc curSt := by
  unfold shouldOverride at h
  split at h
  · rename_i hgt
    exact Or.inl hgt
  · split at h
    · rename_i _ heq
      have heq' : newInc = curInc := uint32_beq_eq heq
      subst heq'
      right
      refine ⟨rfl, ?_⟩
      cases curSt <;> cases newSt <;> simp at h <;> decide
    · contradiction

/-- Equivalence between `shouldOverride` and strict dominance (`Dominates` without equality). -/
theorem shouldOverride_iff_strict_dominates (newInc : Incarnation) (newSt : MemberStatus)
    (curInc : Incarnation) (curSt : MemberStatus) :
    shouldOverride newInc newSt curInc curSt = true ↔
      (Dominates newInc newSt curInc curSt ∧ (newInc ≠ curInc ∨ newSt ≠ curSt)) := by
  constructor
  · intro h
    refine ⟨shouldOverride_implies_dominates newInc newSt curInc curSt h, ?_⟩
    unfold shouldOverride at h
    split at h
    · rename_i hgt
      left
      intro heq
      subst heq
      exact uint32_lt_irrefl newInc hgt
    · split at h
      · right
        cases curSt <;> cases newSt <;> simp_all
      · contradiction
  · rintro ⟨hdom, hne⟩
    unfold shouldOverride
    rcases hdom with hlt | ⟨rfl, hrank⟩
    · simp [hlt]
    · have hnotlt : ¬ (newInc < newInc) := uint32_lt_irrefl newInc
      simp only [hnotlt, ↓reduceIte, beq_self_eq_true]
      rcases hne with hinc | hst
      · exact False.elim (hinc rfl)
      · cases curSt <;> cases newSt <;> simp_all [statusRank] <;> contradiction

/-! ### Member Entry State Monotonicity Predicates -/

/-- Pairwise dominance invariant between two `NodeState` snapshots:
    1. Local self incarnation never decreases.
    2. Membership table size is preserved.
    3. Every member entry at index `i` dominates its prior entry. -/
def StateMonotonic (stBefore stAfter : NodeState) : Prop :=
  stBefore.incarnation ≤ stAfter.incarnation ∧
  stAfter.members.size = stBefore.members.size ∧
  ∀ (i : Nat) (h1 : i < stBefore.members.size) (h2 : i < stAfter.members.size),
    Dominates stAfter.members[i].incarnation stAfter.members[i].status
              stBefore.members[i].incarnation stBefore.members[i].status

theorem stateMonotonic_refl (st : NodeState) : StateMonotonic st st :=
  ⟨Nat.le_refl _, rfl, fun _ _ _ => dominates_refl _ _⟩

theorem stateMonotonic_trans {s1 s2 s3 : NodeState}
    (h12 : StateMonotonic s1 s2) (h23 : StateMonotonic s2 s3) :
    StateMonotonic s1 s3 := by
  rcases h12 with ⟨hinc12, hsz12, hdom12⟩
  rcases h23 with ⟨hinc23, hsz23, hdom23⟩
  refine ⟨Nat.le_trans hinc12 hinc23, hsz23.trans hsz12, fun i h1 h3 => ?_⟩
  have h2 : i < s2.members.size := hsz12 ▸ h1
  exact dominates_trans (hdom23 i h2 h3) (hdom12 i h1 h2)

theorem member_set!_monotonic (members : Array MemberEntry) (idx : Nat) (m' : MemberEntry)
    (hdom : ∀ (h : idx < members.size),
      Dominates m'.incarnation m'.status members[idx].incarnation members[idx].status) :
    (members.set! idx m').size = members.size ∧
    ∀ (i : Nat) (h1 : i < members.size) (h2 : i < (members.set! idx m').size),
      Dominates (members.set! idx m')[i].incarnation (members.set! idx m')[i].status
                members[i].incarnation members[i].status := by
  refine ⟨by simp [Array.set!], ?_⟩
  intro i h1 h2
  simp only [Array.set!] at h2 ⊢
  rw [Array.getElem_setIfInBounds]
  split
  · rename_i heq
    subst heq
    exact hdom h1
  · exact dominates_refl _ _

theorem member_set_monotonic (members : Array MemberEntry) (idx : Nat) (hidx : idx < members.size)
    (m' : MemberEntry)
    (hdom : Dominates m'.incarnation m'.status members[idx].incarnation members[idx].status) :
    (members.set idx m' hidx).size = members.size ∧
    ∀ (i : Nat) (h1 : i < members.size) (h2 : i < (members.set idx m' hidx).size),
      Dominates (members.set idx m' hidx)[i].incarnation (members.set idx m' hidx)[i].status
                members[i].incarnation members[i].status := by
  refine ⟨Array.size_set .., ?_⟩
  intro i h1 h2
  rw [Array.getElem_set]
  split
  · rename_i heq
    subst heq
    exact hdom
  · exact dominates_refl _ _

theorem memberStatus_beq_eq {a b : MemberStatus} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem stateMonotonic_of_eq_fields {s1 s2 : NodeState}
    (hinc : s1.incarnation ≤ s2.incarnation)
    (hmem : s2.members = s1.members) :
    StateMonotonic s1 s2 :=
  ⟨hinc, by rw [hmem], fun i h1 h2 => by
    have heq : s2.members[i] = s1.members[i] := by simp [hmem]
    rw [heq]
    exact dominates_refl _ _⟩

theorem stateMonotonic_preserves_right {s1 s2 s3 : NodeState}
    (h : StateMonotonic s1 s2)
    (hinc : s2.incarnation ≤ s3.incarnation)
    (hmem : s3.members = s2.members) :
    StateMonotonic s1 s3 :=
  stateMonotonic_trans h (stateMonotonic_of_eq_fields hinc hmem)

/-! ### Transition Safety Theorems -/

theorem markSuspect_monotonic (st : NodeState) (targetId : NodeId) (now : Timestamp) :
    StateMonotonic st (markSuspect st targetId now).1 := by
  unfold markSuspect
  split
  · rename_i idx hidx
    dsimp only
    split
    · rename_i halive
      have hidx_lt : idx < st.members.size := by
        have := Array.findIdx?_eq_some_iff_findIdx_eq.mp hidx
        omega
      let m := st.members[idx]!
      let m' := { m with status := .suspect, suspectDeadline := now + st.suspectTimeoutMs }
      have hm_eq : m = st.members[idx] := by simp [m, hidx_lt]
      have halive' : st.members[idx].status = .alive := by
        have h1 : st.members[idx]! = st.members[idx] := by simp [hidx_lt]
        exact memberStatus_beq_eq (by rw [← h1]; exact halive)
      have hdom : ∀ (h : idx < st.members.size),
          Dominates m'.incarnation m'.status st.members[idx].incarnation st.members[idx].status := by
        intro _
        dsimp [m']
        rw [hm_eq, halive']
        exact suspect_dominates_alive _
      have hset := member_set!_monotonic st.members idx m' hdom
      exact ⟨Nat.le_refl _, hset.1, hset.2⟩
    · exact stateMonotonic_refl st
  · exact stateMonotonic_refl st

theorem checkSuspectTimeoutsLoop_monotonic (now : Timestamp) (i : Nat)
    (curMembers : Array MemberEntry) (curBuf : Array GossipUpdate) (acts : Array Action) :
    let res := checkSuspectTimeoutsLoop now i curMembers curBuf acts
    res.1.size = curMembers.size ∧
    ∀ (j : Nat) (h1 : j < curMembers.size) (h2 : j < res.1.size),
      Dominates res.1[j].incarnation res.1[j].status curMembers[j].incarnation curMembers[j].status := by
  induction hrem : curMembers.size - i generalizing i curMembers curBuf acts with
  | zero =>
    dsimp only
    rw [checkSuspectTimeoutsLoop]
    split
    · omega
    · exact ⟨rfl, fun _ _ _ => dominates_refl _ _⟩
  | succ k ih =>
    dsimp only
    rw [checkSuspectTimeoutsLoop]
    have hlt : i < curMembers.size := by omega
    split
    · dsimp only
      split
      · rename_i hcond
        have hst_sus : curMembers[i].status = .suspect :=
          memberStatus_beq_eq ((Bool.and_eq_true _ _).mp hcond |>.1)
        let m' := { curMembers[i] with status := .dead, suspectDeadline := 0 }
        have hdom_step : Dominates m'.incarnation m'.status curMembers[i].incarnation curMembers[i].status := by
          dsimp [m']
          rw [hst_sus]
          exact dead_dominates_suspect _
        have hstep := member_set_monotonic curMembers i hlt m' hdom_step
        have hrem' : (curMembers.set i m' hlt).size - (i + 1) = k := by
          rw [Array.size_set]
          omega
        have h_rec := ih (i + 1) (curMembers.set i m' hlt)
          (addOrUpdate curBuf curMembers[i].id .dead curMembers[i].incarnation)
          (acts.push (.emitMembershipChange curMembers[i].id .dead curMembers[i].incarnation))
          hrem'
        refine ⟨h_rec.1.trans hstep.1, fun j h1 h2 => ?_⟩
        have hmid : j < (curMembers.set i m' hlt).size := hstep.1.symm ▸ h1
        exact dominates_trans (h_rec.2 j hmid h2) (hstep.2 j h1 hmid)
      · have hrem' : curMembers.size - (i + 1) = k := by omega
        exact ih (i + 1) curMembers curBuf acts hrem'
    · omega

theorem checkSuspectTimeouts_monotonic (st : NodeState) (now : Timestamp) :
    StateMonotonic st (checkSuspectTimeouts st now).1 := by
  unfold checkSuspectTimeouts
  have hloop := checkSuspectTimeoutsLoop_monotonic now 0 st.members st.disseminationBuf #[]
  exact ⟨Nat.le_refl _, hloop.1, hloop.2⟩

theorem mergeOneGossipUpdate_monotonic (now : Timestamp) (acc : NodeState × Array Action) (u : GossipUpdate) :
    StateMonotonic acc.1 (mergeOneGossipUpdate now acc u).1 := by
  unfold mergeOneGossipUpdate
  dsimp only
  split
  · -- Update concerning local node
    split
    · rename_i hcond
      have hge : acc.1.incarnation ≤ u.incarnation := by
        have hb := (Bool.and_eq_true _ _).mp hcond |>.2
        simpa using hb
      refine ⟨?_, rfl, fun _ _ _ => dominates_refl _ _⟩
      split
      · rename_i hlt
        have hlt_nat : u.incarnation.toNat < 0xFFFFFFFF := hlt
        have hinc_le : u.incarnation.toNat ≤ (u.incarnation + 1).toNat := by
          have : (u.incarnation + 1).toNat = (u.incarnation.toNat + 1) % 2 ^ 32 := rfl
          omega
        exact Nat.le_trans hge hinc_le
      · exact hge
    · exact stateMonotonic_refl acc.1
  · -- Update concerning a peer
    split
    · rename_i idx hidx
      split
      · rename_i hov
        have hidx_lt : idx < acc.1.members.size := by
          have := Array.findIdx?_eq_some_iff_findIdx_eq.mp hidx
          omega
        let cur := acc.1.members[idx]!
        have hcur_eq : cur = acc.1.members[idx] := by simp [cur, hidx_lt]
        have hdom : ∀ (h : idx < acc.1.members.size),
            Dominates u.incarnation u.status acc.1.members[idx].incarnation acc.1.members[idx].status := by
          intro _
          rw [← hcur_eq]
          exact shouldOverride_implies_dominates u.incarnation u.status cur.incarnation cur.status hov
        let cur' : MemberEntry :=
          { cur with
            status := u.status,
            incarnation := u.incarnation,
            suspectDeadline := if u.status == .suspect then now + acc.1.suspectTimeoutMs else 0 }
        have hset := member_set!_monotonic acc.1.members idx cur' hdom
        exact ⟨Nat.le_refl _, hset.1, hset.2⟩
      · exact stateMonotonic_refl acc.1
    · exact stateMonotonic_of_eq_fields (Nat.le_refl _) rfl

theorem foldl_mergeGossip_monotonic (now : Timestamp) :
    ∀ (l : List GossipUpdate) (acc : NodeState × Array Action),
      StateMonotonic acc.1 (l.foldl (mergeOneGossipUpdate now) acc).1
  | [], acc => stateMonotonic_refl acc.1
  | u :: us, acc =>
    stateMonotonic_trans (mergeOneGossipUpdate_monotonic now acc u)
      (foldl_mergeGossip_monotonic now us (mergeOneGossipUpdate now acc u))

theorem mergeGossipUpdates_monotonic (st : NodeState) (updates : Array GossipUpdate) (now : Timestamp) :
    StateMonotonic st (mergeGossipUpdates st updates now).1 := by
  unfold mergeGossipUpdates
  rw [← Array.foldl_toList]
  exact foldl_mergeGossip_monotonic now updates.toList (st, #[])

private def stepTickTail (now : Timestamp) (curSt : NodeState) (acts : Array Action) : NodeState × Array Action :=
  match checkSuspectTimeouts curSt now with
  | (stAfterTimeouts, timeoutActs) =>
    let acts := acts ++ timeoutActs
    if (stAfterTimeouts.pendingAckDeadline.isNone && decide (now ≥ stAfterTimeouts.nextProbeAt)) = true then
      if stAfterTimeouts.members.isEmpty = true then
        ({ stAfterTimeouts with nextProbeAt := now + stAfterTimeouts.protocolPeriodMs }, acts)
      else
        let idx := stAfterTimeouts.probeIndex % stAfterTimeouts.members.size
        let target := stAfterTimeouts.members[idx]!
        let nextProbeIdx := stAfterTimeouts.probeIndex + 1
        let seq := stAfterTimeouts.seqCounter
        let nextSeq := seq + 1
        let maxTx := calculateMaxTransmissions 3 stAfterTimeouts.members.size
        match drainForPacket stAfterTimeouts.disseminationBuf 6 maxTx with
        | (updates, newBuf) =>
          let msg := Message.ping stAfterTimeouts.selfId seq updates
          let bytes := encodeMessage msg
          let acts := acts.push (Action.sendPacket target.addr bytes)
          ({ stAfterTimeouts with
             disseminationBuf := newBuf,
             seqCounter := nextSeq,
             nextProbeAt := now + stAfterTimeouts.protocolPeriodMs,
             probeIndex := nextProbeIdx,
             pendingAckDeadline := some (target.id, seq, now + stAfterTimeouts.ackTimeoutMs, false) }, acts)
    else
      (stAfterTimeouts, acts)

private theorem stepTickTail_monotonic (now : Timestamp) (curSt : NodeState) (acts : Array Action) :
    StateMonotonic curSt (stepTickTail now curSt acts).1 := by
  unfold stepTickTail
  have hcst := checkSuspectTimeouts_monotonic curSt now
  cases h : checkSuspectTimeouts curSt now with
  | mk stA timeoutActs =>
    dsimp only
    rw [h] at hcst
    split
    · split
      · exact stateMonotonic_preserves_right hcst (Nat.le_refl _) rfl
      · dsimp only
        cases hd : drainForPacket stA.disseminationBuf 6 (calculateMaxTransmissions 3 stA.members.size) with
        | mk updates newBuf =>
          exact stateMonotonic_preserves_right hcst (Nat.le_refl _) rfl
    · exact hcst

theorem stepTick_monotonic (st : NodeState) (now : Timestamp) :
    StateMonotonic st (stepTick st now).1 := by
  have h_eq : (stepTick st now).1 = (match st.pendingAckDeadline with
      | some (targetId, seq, deadline, isIndirect) =>
        if now ≥ deadline then
          if (!isIndirect) = true then
            let candidates :=
              st.members.filter fun (m : MemberEntry) =>
                m.id != targetId && m.id != st.selfId && m.status != MemberStatus.dead
            match pickKRandom candidates 3 st.prngState with
            | (selected, newPrng) =>
              let curSt := { st with prngState := newPrng }
              if selected.isEmpty = true then
                match markSuspect curSt targetId now with
                | (st', suspectActs) =>
                  stepTickTail now { st' with pendingAckDeadline := none } (#[] ++ suspectActs)
              else
                let maxTx := calculateMaxTransmissions 3 curSt.members.size
                let s := Id.run <| forIn selected (#[], curSt.disseminationBuf) fun (helper : MemberEntry) __s =>
                  let acts := __s.fst
                  let curBuf := __s.snd
                  match drainForPacket curBuf 6 maxTx with
                  | (updates, newBuf) =>
                    let msg := Message.pingReq curSt.selfId targetId seq updates
                    let acts := acts.push (Action.sendPacket helper.addr (encodeMessage msg))
                    pure (ForInStep.yield (acts, newBuf))
                stepTickTail now { curSt with disseminationBuf := s.snd, pendingAckDeadline := some (targetId, seq, now + curSt.ackTimeoutMs, true) } s.fst
          else
            match markSuspect st targetId now with
            | (st', suspectActs) =>
              stepTickTail now { st' with pendingAckDeadline := none } (#[] ++ suspectActs)
        else stepTickTail now st #[]
      | none => stepTickTail now st #[]).1 := rfl
  rw [h_eq]
  cases hpend : st.pendingAckDeadline with
  | none => exact stepTickTail_monotonic now st #[]
  | some val =>
    rcases val with ⟨targetId, seq, deadline, isIndirect⟩
    dsimp only
    split
    · split
      · let candidates := st.members.filter fun (m : MemberEntry) =>
          m.id != targetId && m.id != st.selfId && m.status != MemberStatus.dead
        cases hp : pickKRandom candidates 3 st.prngState with
        | mk selected newPrng =>
          dsimp only
          split
          · cases hm : markSuspect
              { st with prngState := newPrng, pendingAckDeadline := some (targetId, seq, deadline, isIndirect) }
              targetId now with
            | mk st' suspectActs =>
              have hms := markSuspect_monotonic
                { st with prngState := newPrng, pendingAckDeadline := some (targetId, seq, deadline, isIndirect) }
                targetId now
              rw [hm] at hms
              dsimp only at hms ⊢
              have h1 : StateMonotonic st { st' with pendingAckDeadline := none } :=
                stateMonotonic_trans (stateMonotonic_of_eq_fields (Nat.le_refl _) rfl)
                  (stateMonotonic_preserves_right hms (Nat.le_refl _) rfl)
              refine stateMonotonic_trans h1
                (stepTickTail_monotonic now { st' with pendingAckDeadline := none } (#[] ++ suspectActs))
          · have h_mono : ∀ (cs' : NodeState) (acts' : Array Action),
                st.incarnation ≤ cs'.incarnation → cs'.members = st.members →
                StateMonotonic st (stepTickTail now cs' acts').1 := fun cs' acts' hi hm =>
                  stateMonotonic_trans (stateMonotonic_of_eq_fields hi hm) (stepTickTail_monotonic now cs' acts')
            exact h_mono _ _ (Nat.le_refl _) rfl
      · cases hm : markSuspect st targetId now with
        | mk st' suspectActs =>
          have hms := markSuspect_monotonic st targetId now
          rw [hm] at hms
          dsimp only at hms ⊢
          have h1 : StateMonotonic st { st' with pendingAckDeadline := none } :=
            stateMonotonic_preserves_right hms (Nat.le_refl _) rfl
          exact stateMonotonic_trans h1
            (stepTickTail_monotonic now { st' with pendingAckDeadline := none } (#[] ++ suspectActs))
    · exact stepTickTail_monotonic now st #[]

theorem stepRecvPacket_monotonic (st : NodeState) (src : PeerAddr) (payload : ByteArray) (now : Timestamp) :
    StateMonotonic st (stepRecvPacket st src payload now).1 := by
  unfold stepRecvPacket
  dsimp only [Id.run, pure]
  split
  · exact stateMonotonic_refl st
  · rename_i msg _
    cases msg with
    | ping srcNodeId seq updates =>
      dsimp only
      have hm := mergeGossipUpdates_monotonic st updates now
      cases hmg : mergeGossipUpdates st updates now with
      | mk st1 updateActs =>
        dsimp only
        rw [hmg] at hm
        cases hd : drainForPacket st1.disseminationBuf 6 (calculateMaxTransmissions 3 st1.members.size) with
        | mk piggyUpdates newBuf =>
          exact stateMonotonic_preserves_right hm (Nat.le_refl _) rfl
    | pingReq reqSrc targetId seq updates =>
      dsimp only
      have hm := mergeGossipUpdates_monotonic st updates now
      cases hmg : mergeGossipUpdates st updates now with
      | mk st1 updateActs =>
        dsimp only
        rw [hmg] at hm
        split
        · dsimp only
          cases hd : drainForPacket st1.disseminationBuf 6 (calculateMaxTransmissions 3 st1.members.size) with
          | mk piggyUpdates newBuf =>
            exact stateMonotonic_preserves_right hm (Nat.le_refl _) rfl
        · exact hm
    | ack src seq updates =>
      dsimp only
      have hm := mergeGossipUpdates_monotonic st updates now
      cases hmg : mergeGossipUpdates st updates now with
      | mk st1 updateActs =>
        dsimp only
        rw [hmg] at hm
        split
        · split
          · split <;> exact stateMonotonic_preserves_right hm (Nat.le_refl _) rfl
          · split <;> exact stateMonotonic_preserves_right hm (Nat.le_refl _) rfl
        · split <;> exact stateMonotonic_preserves_right hm (Nat.le_refl _) rfl

/-- **Master Transition Safety Theorem**: Every transition of `SwimCore.step` (timer tick or
    packet reception) preserves `StateMonotonic`: self incarnation never decreases, member table
    size is preserved, and every member entry is non-decreasing in the `Dominates` join-semilattice. -/
theorem step_preserves_safety (st : NodeState) (ev : Event) :
    StateMonotonic st (step st ev).1 := by
  unfold step
  cases ev with
  | tick now => exact stepTick_monotonic st now
  | recvPacket src payload now => exact stepRecvPacket_monotonic st src payload now

end SwimProofs

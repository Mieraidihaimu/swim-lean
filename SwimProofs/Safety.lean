import SwimCore.Types

/-!
# SWIM Deterministic Safety Theorems

This module formalizes the information ordering and join-semilattice on
SWIM member state tuples: `(Incarnation × MemberStatus)`.

## Protocol Safety Principles
1. **Incarnation Precedence**: A higher incarnation number strictly dominates any
   status with a lower incarnation number.
2. **Monotonic Status Ordering at Equal Incarnation**: At the same incarnation,
   the status progresses monotonically:
   `alive < suspect < dead`.
   Specifically:
   - `dead` dominates `suspect` and `alive`.
   - `suspect` dominates `alive`.
3. **Absorption of Dead**: At equal incarnation, `dead` is absorbing; no lower status
   can override `dead`.
4. **Join-Semilattice Merge**: The `mergeStatus` operator computes the least upper bound
   (supremum) of two membership observations, guaranteeing that local state updates
   are monotonic and non-regressive (`Dominates (mergeStatus l i) l`).
-/

namespace SwimProofs

open SwimCore

/-- Numerical rank of `MemberStatus` reflecting information completeness:
    `alive` (0) < `suspect` (1) < `dead` (2). -/
def statusRank : MemberStatus → Nat
  | .alive   => 0
  | .suspect => 1
  | .dead    => 2

/-- Dominance relation (information ordering) on `(Incarnation × MemberStatus)`.
    `Dominates inc1 st1 inc2 st2` holds when `(inc1, st1)` carries at least as much
    up-to-date protocol information as `(inc2, st2)`. -/
def Dominates (inc1 : Incarnation) (st1 : MemberStatus) (inc2 : Incarnation) (st2 : MemberStatus) : Prop :=
  inc2 < inc1 ∨ (inc1 = inc2 ∧ statusRank st2 ≤ statusRank st1)

/-- `Dominates` is decidable for all incarnation and status pairs. -/
instance (inc1 : Incarnation) (st1 : MemberStatus) (inc2 : Incarnation) (st2 : MemberStatus) :
    Decidable (Dominates inc1 st1 inc2 st2) := by
  dsimp [Dominates]
  infer_instance

/-! ### Arithmetic & Ordering Foundations for `UInt32` -/

theorem uint32_lt_asymm {a b : UInt32} (h1 : a < b) (h2 : b < a) : False := by
  have h1' : a.toNat < b.toNat := h1
  have h2' : b.toNat < a.toNat := h2
  exact Nat.lt_asymm h1' h2'

theorem uint32_lt_irrefl (a : UInt32) : ¬ a < a :=
  fun h => uint32_lt_asymm h h

theorem uint32_lt_trans {a b c : UInt32} (h1 : a < b) (h2 : b < c) : a < c := by
  have h1' : a.toNat < b.toNat := h1
  have h2' : b.toNat < c.toNat := h2
  exact Nat.lt_trans h1' h2'

theorem uint32_eq_of_not_lt_and_not_lt {a b : UInt32} (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b := by
  have h1' : ¬ a.toNat < b.toNat := h1
  have h2' : ¬ b.toNat < a.toNat := h2
  have heq : a.toNat = b.toNat := by omega
  rcases a with ⟨a'⟩
  rcases b with ⟨b'⟩
  have heq' : a' = b' := BitVec.eq_of_toNat_eq heq
  subst heq'
  rfl

theorem statusRank_injective {s1 s2 : MemberStatus} (h : statusRank s1 = statusRank s2) : s1 = s2 := by
  cases s1 <;> cases s2 <;> first | rfl | contradiction

/-! ### Core Dominance Properties: Reflexivity, Transitivity, Antisymmetry, Totality -/

/-- Reflexivity: Any status observation dominates itself. -/
theorem dominates_refl (inc : Incarnation) (st : MemberStatus) :
    Dominates inc st inc st := by
  right
  exact ⟨rfl, Nat.le_refl (statusRank st)⟩

/-- Transitivity: Information dominance is transitive. -/
theorem dominates_trans {inc1 inc2 inc3 : Incarnation} {st1 st2 st3 : MemberStatus}
    (h12 : Dominates inc1 st1 inc2 st2) (h23 : Dominates inc2 st2 inc3 st3) :
    Dominates inc1 st1 inc3 st3 := by
  rcases h12 with h12_lt | ⟨rfl, h12_rank⟩
  · rcases h23 with h23_lt | ⟨rfl, _⟩
    · left; exact uint32_lt_trans h23_lt h12_lt
    · left; exact h12_lt
  · rcases h23 with h23_lt | ⟨rfl, h23_rank⟩
    · left; exact h23_lt
    · right
      refine ⟨rfl, Nat.le_trans h23_rank h12_rank⟩

/-- Antisymmetry: Mutual dominance implies identical incarnation and status. -/
theorem dominates_antisymm {inc1 inc2 : Incarnation} {st1 st2 : MemberStatus}
    (h12 : Dominates inc1 st1 inc2 st2) (h21 : Dominates inc2 st2 inc1 st1) :
    inc1 = inc2 ∧ st1 = st2 := by
  rcases h12 with h12_lt | ⟨rfl, h12_rank⟩
  · rcases h21 with h21_lt | ⟨rfl, _⟩
    · exact False.elim (uint32_lt_asymm h12_lt h21_lt)
    · exact False.elim (uint32_lt_asymm h12_lt h12_lt)
  · rcases h21 with h21_lt | ⟨_, h21_rank⟩
    · exact False.elim (uint32_lt_asymm h21_lt h21_lt)
    · have hrank_eq : statusRank st1 = statusRank st2 := Nat.le_antisymm h21_rank h12_rank
      have hst_eq := statusRank_injective hrank_eq
      exact ⟨rfl, hst_eq⟩

/-- Totality: Any two membership observations are comparable under `Dominates`. -/
theorem dominates_total (inc1 : Incarnation) (st1 : MemberStatus) (inc2 : Incarnation) (st2 : MemberStatus) :
    Dominates inc1 st1 inc2 st2 ∨ Dominates inc2 st2 inc1 st1 := by
  by_cases hlt1 : inc2 < inc1
  · left; left; exact hlt1
  · by_cases hlt2 : inc1 < inc2
    · right; left; exact hlt2
    · have heq := uint32_eq_of_not_lt_and_not_lt hlt2 hlt1
      subst heq
      by_cases hrank : statusRank st2 ≤ statusRank st1
      · left; right; exact ⟨rfl, hrank⟩
      · right; right
        have hrank2 : statusRank st1 ≤ statusRank st2 := Nat.le_of_not_le hrank
        exact ⟨rfl, hrank2⟩

/-! ### Protocol-Specific Ordering Theorems -/

/-- Rule 1: A strictly higher incarnation dominates any status with a lower incarnation. -/
theorem higher_incarnation_strictly_dominates (inc1 inc2 : Incarnation) (st1 st2 : MemberStatus)
    (h : inc2 < inc1) : Dominates inc1 st1 inc2 st2 :=
  Or.inl h

/-- Rule 2a: At equal incarnation, `dead` dominates `suspect`. -/
theorem dead_dominates_suspect (inc : Incarnation) : Dominates inc .dead inc .suspect := by
  right; exact ⟨rfl, by decide⟩

/-- Rule 2b: At equal incarnation, `suspect` dominates `alive`. -/
theorem suspect_dominates_alive (inc : Incarnation) : Dominates inc .suspect inc .alive := by
  right; exact ⟨rfl, by decide⟩

/-- Rule 2c: At equal incarnation, `dead` dominates `alive`. -/
theorem dead_dominates_alive (inc : Incarnation) : Dominates inc .dead inc .alive := by
  right; exact ⟨rfl, by decide⟩

/-! ### Absorption Theorems for `dead` -/

/-- At the same incarnation, `dead` dominates all other statuses. -/
theorem dead_dominates_all_at_same_inc (inc : Incarnation) (st : MemberStatus) :
    Dominates inc .dead inc st := by
  right
  refine ⟨rfl, ?_⟩
  cases st <;> decide

/-- At the same incarnation, only `dead` can dominate `dead`. -/
theorem only_dead_dominates_dead_at_same_inc (inc : Incarnation) (st : MemberStatus) :
    Dominates inc st inc .dead → st = .dead := by
  intro h
  rcases h with hlt | ⟨_, hle⟩
  · exact False.elim (uint32_lt_irrefl inc hlt)
  · cases st with
    | alive => contradiction
    | suspect => contradiction
    | dead => rfl

/-! ### Status Merge Function & Join-Semilattice Properties -/

/-- Merges a local node membership record with an incoming gossip update.
    Returns the least upper bound according to the `Dominates` information ordering. -/
def mergeStatus (localInc : Incarnation) (localSt : MemberStatus)
                (incomingInc : Incarnation) (incomingSt : MemberStatus) : Incarnation × MemberStatus :=
  if localInc < incomingInc then
    (incomingInc, incomingSt)
  else if incomingInc < localInc then
    (localInc, localSt)
  else
    if statusRank localSt ≤ statusRank incomingSt then
      (incomingInc, incomingSt)
    else
      (localInc, localSt)

/-- The merge result is idempotent: merging identical state returns itself. -/
theorem mergeStatus_idempotent (inc : Incarnation) (st : MemberStatus) :
    mergeStatus inc st inc st = (inc, st) := by
  dsimp [mergeStatus]
  have nirr := uint32_lt_irrefl inc
  split
  · contradiction
  · split
    · rfl
    · rfl

/-- If the local state dominates the incoming state, the merge result is the local state. -/
theorem mergeStatus_of_dominates_left {inc1 inc2 : Incarnation} {st1 st2 : MemberStatus}
    (h : Dominates inc1 st1 inc2 st2) :
    mergeStatus inc1 st1 inc2 st2 = (inc1, st1) := by
  dsimp [mergeStatus]
  rcases h with hlt | ⟨rfl, hrank⟩
  · split
    · rename_i h1; exact False.elim (uint32_lt_asymm hlt h1)
    · rfl
  · have nirr := uint32_lt_irrefl inc1
    split
    · contradiction
    · split
      · cases st1 <;> cases st2 <;> first | rfl | contradiction
      · rfl

/-- If the incoming state dominates the local state, the merge result is the incoming state. -/
theorem mergeStatus_of_dominates_right {inc1 inc2 : Incarnation} {st1 st2 : MemberStatus}
    (h : Dominates inc1 st1 inc2 st2) :
    mergeStatus inc2 st2 inc1 st1 = (inc1, st1) := by
  dsimp [mergeStatus]
  rcases h with hlt | ⟨rfl, hrank⟩
  · split
    · rfl
    · contradiction
  · have nirr := uint32_lt_irrefl inc1
    split
    · contradiction
    · rfl

/-- Characterization of `mergeStatus` as an `if-then-else` on `Dominates`. -/
theorem mergeStatus_eq_ite (inc1 : Incarnation) (st1 : MemberStatus)
                           (inc2 : Incarnation) (st2 : MemberStatus) :
    mergeStatus inc1 st1 inc2 st2 = if Dominates inc1 st1 inc2 st2 then (inc1, st1) else (inc2, st2) := by
  split
  · rename_i hdom
    exact mergeStatus_of_dominates_left hdom
  · rename_i hnot
    rcases dominates_total inc1 st1 inc2 st2 with h1 | h2
    · exact False.elim (hnot h1)
    · exact mergeStatus_of_dominates_right h2

/-- Commutativity: `mergeStatus` is symmetric with respect to operand order. -/
theorem mergeStatus_comm (inc1 : Incarnation) (st1 : MemberStatus)
                         (inc2 : Incarnation) (st2 : MemberStatus) :
    mergeStatus inc1 st1 inc2 st2 = mergeStatus inc2 st2 inc1 st1 := by
  rcases dominates_total inc1 st1 inc2 st2 with h1 | h2
  · rw [mergeStatus_of_dominates_left h1, mergeStatus_of_dominates_right h1]
  · rw [mergeStatus_of_dominates_right h2, mergeStatus_of_dominates_left h2]

/-- Safety Theorem: Merging any incoming status always results in a state that
    dominates the prior local state (monotonic progress). -/
theorem mergeStatus_dominates_local (localInc : Incarnation) (localSt : MemberStatus)
                                   (incomingInc : Incarnation) (incomingSt : MemberStatus) :
    let res := mergeStatus localInc localSt incomingInc incomingSt
    Dominates res.1 res.2 localInc localSt := by
  intro res
  change Dominates (mergeStatus localInc localSt incomingInc incomingSt).1
                   (mergeStatus localInc localSt incomingInc incomingSt).2
                   localInc localSt
  dsimp [mergeStatus]
  split
  · rename_i h1
    left; exact h1
  · split
    · rename_i _ _
      right; exact ⟨rfl, Nat.le_refl _⟩
    · split
      · rename_i h1 h2 h3
        have heq := uint32_eq_of_not_lt_and_not_lt h1 h2
        right
        exact ⟨heq.symm, h3⟩
      · rename_i _ _ _
        right; exact ⟨rfl, Nat.le_refl _⟩

/-- Merging also produces a state that dominates the incoming status. -/
theorem mergeStatus_dominates_incoming (localInc : Incarnation) (localSt : MemberStatus)
                                      (incomingInc : Incarnation) (incomingSt : MemberStatus) :
    let res := mergeStatus localInc localSt incomingInc incomingSt
    Dominates res.1 res.2 incomingInc incomingSt := by
  intro res
  change Dominates (mergeStatus localInc localSt incomingInc incomingSt).1
                   (mergeStatus localInc localSt incomingInc incomingSt).2
                   incomingInc incomingSt
  dsimp [mergeStatus]
  split
  · rename_i _
    right; exact ⟨rfl, Nat.le_refl _⟩
  · split
    · rename_i _ h2
      left; exact h2
    · split
      · rename_i _ _ _
        right; exact ⟨rfl, Nat.le_refl _⟩
      · rename_i h1 h2 h3
        have heq := uint32_eq_of_not_lt_and_not_lt h1 h2
        right
        refine ⟨heq, ?_⟩
        have hrank : ¬ (statusRank localSt ≤ statusRank incomingSt) := h3
        exact Nat.le_of_not_le hrank

/-- Least Upper Bound: Any state that dominates both inputs also dominates their merge. -/
theorem mergeStatus_least_upper_bound {inc1 inc2 inc3 : Incarnation} {st1 st2 st3 : MemberStatus}
    (h1 : Dominates inc3 st3 inc1 st1) (h2 : Dominates inc3 st3 inc2 st2) :
    let m := mergeStatus inc1 st1 inc2 st2
    Dominates inc3 st3 m.1 m.2 := by
  intro m
  change Dominates inc3 st3 (mergeStatus inc1 st1 inc2 st2).1 (mergeStatus inc1 st1 inc2 st2).2
  rw [mergeStatus_eq_ite]
  split
  · exact h1
  · exact h2

/-- Dead Absorption under Merge (Left): Merging with a local `dead` state at the same
    incarnation absorbs the incoming status and remains `dead`. -/
theorem mergeStatus_dead_absorbing_left (inc : Incarnation) (incomingSt : MemberStatus) :
    mergeStatus inc .dead inc incomingSt = (inc, .dead) := by
  dsimp [mergeStatus]
  have nirr := uint32_lt_irrefl inc
  split
  · contradiction
  · split
    · cases incomingSt with
      | alive => contradiction
      | suspect => contradiction
      | dead => rfl
    · rfl

/-- Dead Absorption under Merge (Right): Merging any local state with an incoming `dead`
    state at the same incarnation transitions to `dead`. -/
theorem mergeStatus_dead_absorbing_right (inc : Incarnation) (localSt : MemberStatus) :
    mergeStatus inc localSt inc .dead = (inc, .dead) := by
  dsimp [mergeStatus]
  have nirr := uint32_lt_irrefl inc
  split
  · contradiction
  · split
    · rfl
    · cases localSt with
      | alive => contradiction
      | suspect => contradiction
      | dead => contradiction

end SwimProofs

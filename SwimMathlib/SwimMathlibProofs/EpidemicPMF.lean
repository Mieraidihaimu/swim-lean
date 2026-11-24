import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Finset.Card

/-!
# Axiom-Free Mathlib4 Epidemic Push-Gossip PMF Model & Phase 2 Convergence

This module replaces all placeholder real-number axioms with genuine `Mathlib4`
theorems over `PMF`, `Finset`, `ℝ≥0∞`, and `ℝ`.

## Model
- Cluster of `n` nodes (`2 ≤ n`), indexed by `Fin n`.
- A round of push-gossip from infected set `S : Finset (Fin n)` selects `S.card`
  destinations independently and uniformly from `Fin n` (`kPicks n S.card S`).
- Every state in the support of `pushRoundPMF n S` is a superset of `S` (monotonicity).
- Single-node escape probability: for any fixed `w ∉ S`, the probability `w`
  remains uninfected after `k` uniform picks is `(1 - 1 / n) ^ k`.
- Phase 2 (`(n : ℝ) / 2 ≤ S.card`): over `R` rounds, union bound failure probability
  is `≤ n * Real.exp (-R / 2)`, so for `R ≥ 2 * (c + 1) * Real.log n`, failure
  probability is `≤ (n : ℝ) ^ (-c)` with zero axioms and zero `sorry`.
-/

namespace SwimMathlibProofs

open scoped BigOperators ENNReal

/-- Uniform probability distribution over `Fin n` (for `n > 0`). -/
noncomputable def uniformNode (n : ℕ) [NeZero n] : PMF (Fin n) :=
  PMF.ofFintype (fun _ => (n : ℝ≥0∞)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (NeZero.natCast_ne n ℝ≥0∞) (ENNReal.natCast_ne_top n))

@[simp]
theorem uniformNode_apply (n : ℕ) [NeZero n] (x : Fin n) :
    uniformNode n x = (n : ℝ≥0∞)⁻¹ := rfl

/-- One infected node chooses a peer uniformly at random and infects it. -/
noncomputable def pickOne (n : ℕ) [NeZero n] (S : Finset (Fin n)) : PMF (Finset (Fin n)) :=
  (uniformNode n).bind fun v => PMF.pure (insert v S)

/-- `k` sequential independent uniform peer selections starting from `S`. -/
noncomputable def kPicks (n : ℕ) [NeZero n] : ℕ → Finset (Fin n) → PMF (Finset (Fin n))
  | 0, S => PMF.pure S
  | k + 1, S => (pickOne n S).bind (kPicks n k)

/-- One synchronous round of push-gossip from infected set `S`:
    each of the `S.card` infected nodes picks one random target. -/
noncomputable def pushRoundPMF (n : ℕ) [NeZero n] (S : Finset (Fin n)) : PMF (Finset (Fin n)) :=
  kPicks n S.card S

/-- `R` consecutive rounds of synchronous push-gossip starting from `S`. -/
noncomputable def runRounds (n : ℕ) [NeZero n] : ℕ → Finset (Fin n) → PMF (Finset (Fin n))
  | 0, S => PMF.pure S
  | R + 1, S => (pushRoundPMF n S).bind (runRounds n R)

/-! ### Finite Probability Helpers -/

/-- Exact probability of a decidable predicate under a `PMF` on a finite type. -/
noncomputable def prob {α : Type*} [Fintype α] (p : PMF α) (P : α → Prop) [DecidablePred P] : ℝ≥0∞ :=
  ∑ a : α, if P a then p a else 0

/-- Real-valued probability of a decidable predicate under a `PMF` on a finite type. -/
noncomputable def probR {α : Type*} [Fintype α] (p : PMF α) (P : α → Prop) [DecidablePred P] : ℝ :=
  (prob p P).toReal

theorem prob_eq_tsum {α : Type*} [Fintype α] (p : PMF α) (P : α → Prop) [DecidablePred P] :
    prob p P = ∑' a : α, if P a then p a else 0 := by
  rw [prob, tsum_fintype]

theorem prob_le_one {α : Type*} [Fintype α] (p : PMF α) (P : α → Prop) [DecidablePred P] :
    prob p P ≤ 1 := by
  calc
    prob p P = ∑ a : α, if P a then p a else 0 := rfl
    _ ≤ ∑ a : α, p a := by
      refine Finset.sum_le_sum fun a _ => ?_
      split_ifs <;> simp
    _ = ∑' a : α, p a := (tsum_fintype _).symm
    _ = 1 := p.tsum_coe

theorem prob_ne_top {α : Type*} [Fintype α] (p : PMF α) (P : α → Prop) [DecidablePred P] :
    prob p P ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_one p P)

theorem probR_nonneg {α : Type*} [Fintype α] (p : PMF α) (P : α → Prop) [DecidablePred P] :
    0 ≤ probR p P := ENNReal.toReal_nonneg

theorem probR_le_one {α : Type*} [Fintype α] (p : PMF α) (P : α → Prop) [DecidablePred P] :
    probR p P ≤ 1 := by
  rw [probR, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one p P)

theorem prob_pure {α : Type*} [Fintype α] [DecidableEq α] (x : α)
    (P : α → Prop) [DecidablePred P] :
    prob (PMF.pure x) P = if P x then 1 else 0 := by
  rw [prob]
  simp only [PMF.pure_apply]
  trans ∑ a : α, (if a = x then (if P x then (1 : ℝ≥0∞) else 0) else 0)
  · refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = x
    · subst ha; simp
    · simp [ha]
  · simp [Finset.sum_ite_eq']

theorem prob_bind {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → PMF β) (P : β → Prop) [DecidablePred P] :
    prob (p.bind f) P = ∑ a : α, p a * prob (f a) P := by
  rw [prob]
  simp_rw [PMF.bind_apply, tsum_fintype]
  have hswap : (∑ b : β, if P b then ∑ a : α, p a * f a b else 0) =
      ∑ b : β, ∑ a : α, (if P b then p a * f a b else 0) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [hswap, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [prob, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

theorem prob_mono {α : Type*} [Fintype α] (p : PMF α)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ a, P a → Q a) :
    prob p P ≤ prob p Q := by
  refine Finset.sum_le_sum fun a _ => ?_
  split_ifs with hP hQ
  · exact le_rfl
  · exact False.elim (hQ (hPQ a hP))
  · simp
  · exact le_rfl

theorem probR_mono {α : Type*} [Fintype α] (p : PMF α)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ a, P a → Q a) :
    probR p P ≤ probR p Q :=
  ENNReal.toReal_mono (prob_ne_top p Q) (prob_mono p P Q hPQ)

theorem prob_union_le_finset {α ι : Type*} [Fintype α]
    (p : PMF α) (s : Finset ι) (P : ι → α → Prop)
    [∀ i, DecidablePred (P i)] [DecidablePred (fun a => ∃ i ∈ s, P i a)] :
    prob p (fun a => ∃ i ∈ s, P i a) ≤ ∑ i ∈ s, prob p (P i) := by
  classical
  calc
    prob p (fun a => ∃ i ∈ s, P i a)
        = ∑ a : α, if ∃ i ∈ s, P i a then p a else 0 := rfl
    _ ≤ ∑ a : α, ∑ i ∈ s, (if P i a then p a else 0) := by
      refine Finset.sum_le_sum fun a _ => ?_
      split_ifs with hex
      · rcases hex with ⟨i, hi, hPi⟩
        have hle : (if P i a then p a else 0) ≤ ∑ j ∈ s, (if P j a then p a else 0) :=
          Finset.single_le_sum (f := fun j => if P j a then p a else 0) (fun _ _ => by simp) hi
        simpa [hPi] using hle
      · simp
    _ = ∑ i ∈ s, ∑ a : α, (if P i a then p a else 0) := Finset.sum_comm
    _ = ∑ i ∈ s, prob p (P i) := rfl

/-! ### Support Monotonicity of Push-Gossip -/

theorem pickOne_support_subset {n : ℕ} [NeZero n] {S S' : Finset (Fin n)}
    (h : S' ∈ (pickOne n S).support) : S ⊆ S' := by
  rw [pickOne, PMF.mem_support_bind_iff] at h
  rcases h with ⟨v, _, hv⟩
  rw [PMF.mem_support_pure_iff] at hv
  subst hv
  exact Finset.subset_insert v S

theorem kPicks_support_subset {n : ℕ} [NeZero n] :
    ∀ (k : ℕ) {S S' : Finset (Fin n)}, S' ∈ (kPicks n k S).support → S ⊆ S'
  | 0, _, _, h => by
    rw [kPicks, PMF.mem_support_pure_iff] at h
    subst h; exact Finset.Subset.rfl
  | k + 1, S, S', h => by
    rw [kPicks, PMF.mem_support_bind_iff] at h
    rcases h with ⟨Smid, h1, h2⟩
    exact Finset.Subset.trans (pickOne_support_subset h1) (kPicks_support_subset k h2)

theorem pushRoundPMF_support_subset {n : ℕ} [NeZero n] {S S' : Finset (Fin n)}
    (h : S' ∈ (pushRoundPMF n S).support) : S ⊆ S' :=
  kPicks_support_subset S.card h

theorem runRounds_support_subset {n : ℕ} [NeZero n] :
    ∀ (R : ℕ) {S S' : Finset (Fin n)}, S' ∈ (runRounds n R S).support → S ⊆ S'
  | 0, _, _, h => by
    rw [runRounds, PMF.mem_support_pure_iff] at h
    subst h; exact Finset.Subset.rfl
  | R + 1, S, S', h => by
    rw [runRounds, PMF.mem_support_bind_iff] at h
    rcases h with ⟨Smid, h1, h2⟩
    exact Finset.Subset.trans (pushRoundPMF_support_subset h1) (runRounds_support_subset R h2)

/-! ### Exact Single-Node Escape Probability in PMF -/

/-- Single-draw non-infection probability: if `w ∉ S`, then after one uniform pick
    from `Fin n`, `w` stays uninfected with probability `(n - 1) / n`. -/
theorem prob_pickOne_notMem {n : ℕ} [NeZero n] (S : Finset (Fin n)) (w : Fin n) (hw : w ∉ S) :
    prob (pickOne n S) (fun S' => w ∉ S') = ((n - 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞) := by
  rw [pickOne, prob_bind]
  have hterm : ∀ v : Fin n, uniformNode n v * prob (PMF.pure (insert v S)) (fun S' => w ∉ S') =
      if v = w then 0 else (n : ℝ≥0∞)⁻¹ := by
    intro v
    rw [uniformNode_apply, prob_pure]
    by_cases hv : v = w
    · subst hv; simp
    · have hnotin : w ∉ insert v S := by simp [Ne.symm hv, hw]
      simp [hv, hnotin]
  simp_rw [hterm]
  rw [← Finset.add_sum_erase Finset.univ (fun v : Fin n => if v = w then (0 : ℝ≥0∞) else (n : ℝ≥0∞)⁻¹) (Finset.mem_univ w)]
  simp only [↓reduceIte, zero_add]
  have hcongr : ∑ v ∈ Finset.univ.erase w, (if v = w then (0 : ℝ≥0∞) else (n : ℝ≥0∞)⁻¹) =
      ∑ _v ∈ Finset.univ.erase w, (n : ℝ≥0∞)⁻¹ := by
    refine Finset.sum_congr rfl fun v hv => ?_
    have hne : v ≠ w := (Finset.mem_erase.mp hv).1
    simp [hne]
  rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ w),
      Finset.card_fin, nsmul_eq_mul, div_eq_mul_inv]

/-- If `w ∈ S`, then after one pick `w` is definitely in `S'`, so escape probability is `0`. -/
theorem prob_pickOne_notMem_of_mem {n : ℕ} [NeZero n] (S : Finset (Fin n)) (w : Fin n) (hw : w ∈ S) :
    prob (pickOne n S) (fun S' => w ∉ S') = 0 := by
  rw [pickOne, prob_bind]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [prob_pure]
  have hmem : w ∈ insert v S := Finset.mem_insert_of_mem hw
  simp [hmem]

/-- Exact `k`-pick escape probability:
    for any `w ∉ S`, the probability `w` avoids all `k` draws is `((n - 1) / n) ^ k`. -/
theorem prob_kPicks_notMem {n : ℕ} [NeZero n] :
    ∀ (k : ℕ) (S : Finset (Fin n)) (w : Fin n), w ∉ S →
      prob (kPicks n k S) (fun S' => w ∉ S') = (((n - 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ k
  | 0, S, w, hw => by
    rw [kPicks, prob_pure]
    simp [hw]
  | k + 1, S, w, hw => by
    rw [kPicks, prob_bind]
    have hcongr : (∑ S1 : Finset (Fin n), pickOne n S S1 * prob (kPicks n k S1) (fun S' => w ∉ S')) =
        ∑ S1 : Finset (Fin n),
          if w ∉ S1 then pickOne n S S1 * (((n - 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ k else 0 := by
      refine Finset.sum_congr rfl fun S1 _ => ?_
      by_cases h1 : w ∈ S1
      · have hz : prob (kPicks n k S1) (fun S' => w ∉ S') = 0 := by
          rw [prob]
          refine Finset.sum_eq_zero fun S' _ => ?_
          by_cases hsupp : S' ∈ (kPicks n k S1).support
          · have hsub : S1 ⊆ S' := kPicks_support_subset k hsupp
            simp [hsub h1]
          · rw [PMF.mem_support_iff, not_not] at hsupp
            split_ifs <;> simp [hsupp]
        simp [h1, hz]
      · simp [h1, prob_kPicks_notMem k S1 w h1]
    rw [hcongr]
    have hfactor : (∑ S1 : Finset (Fin n),
        if w ∉ S1 then pickOne n S S1 * (((n - 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ k else 0) =
        (∑ S1 : Finset (Fin n), if w ∉ S1 then pickOne n S S1 else 0) *
          (((n - 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ k := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun S1 _ => ?_
      split_ifs <;> simp
    rw [hfactor]
    change prob (pickOne n S) (fun S1 => w ∉ S1) * (((n - 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ^ k = _
    rw [prob_pickOne_notMem S w hw, pow_succ']

/-- In real arithmetic, `probR (pushRoundPMF n S) (fun S' => w ∉ S') = (1 - 1 / n) ^ S.card`. -/
theorem probR_pushRound_notMem {n : ℕ} [NeZero n] (hn : 2 ≤ n) (S : Finset (Fin n)) (w : Fin n) (hw : w ∉ S) :
    probR (pushRoundPMF n S) (fun S' => w ∉ S') = (1 - 1 / (n : ℝ)) ^ S.card := by
  rw [probR, pushRoundPMF, prob_kPicks_notMem S.card S w hw]
  have hn_pos : (0 : ℝ) < n := by positivity
  have hn1 : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hn1
    linarith
  rw [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, hcast]
  congr 1
  field_simp

/-- If `S.card ≥ n / 2` (Phase 2), the single-round escape probability of ANY `w` is at most
    `Real.exp (-1/2)`. -/
theorem probR_pushRound_notMem_le_exp_neg_half {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (S : Finset (Fin n)) (hP2 : (n : ℝ) / 2 ≤ S.card) (w : Fin n) :
    probR (pushRoundPMF n S) (fun S' => w ∉ S') ≤ Real.exp (-(1 / 2 : ℝ)) := by
  by_cases hw : w ∈ S
  · have hzero : prob (pushRoundPMF n S) (fun S' => w ∉ S') = 0 := by
      rw [prob]
      refine Finset.sum_eq_zero fun S' _ => ?_
      by_cases hsupp : S' ∈ (pushRoundPMF n S).support
      · simp [pushRoundPMF_support_subset hsupp hw]
      · rw [PMF.mem_support_iff, not_not] at hsupp
        split_ifs <;> simp [hsupp]
    have h0 : probR (pushRoundPMF n S) (fun S' => w ∉ S') = 0 := by
      rw [probR, hzero, ENNReal.toReal_zero]
    rw [h0]
    exact (Real.exp_pos _).le
  · rw [probR_pushRound_notMem hn S w hw]
    have hn_pos : (0 : ℝ) < n := by positivity
    have hbase_nonneg : 0 ≤ 1 - 1 / (n : ℝ) := by
      have : 1 / (n : ℝ) ≤ 1 := div_le_self zero_le_one (by exact_mod_cast (by omega : 1 ≤ n))
      linarith
    have hbase_exp : 1 - 1 / (n : ℝ) ≤ Real.exp (-(1 / (n : ℝ))) := by
      have := Real.add_one_le_exp (-(1 / (n : ℝ)))
      linarith
    have hpow : (1 - 1 / (n : ℝ)) ^ S.card ≤ (Real.exp (-(1 / (n : ℝ)))) ^ S.card :=
      pow_le_pow_left₀ hbase_nonneg hbase_exp S.card
    have hexp_mul : (Real.exp (-(1 / (n : ℝ)))) ^ S.card = Real.exp (-((S.card : ℝ) / n)) := by
      rw [← Real.exp_nat_mul]
      congr 1; ring
    have hratio : -(1 / 2 : ℝ) ≥ -((S.card : ℝ) / n) := by
      have : (1 / 2 : ℝ) ≤ (S.card : ℝ) / n := (le_div_iff₀ hn_pos).mpr (by linarith)
      linarith
    exact le_trans hpow (by rw [hexp_mul]; exact Real.exp_le_exp.mpr hratio)

/-! ### Phase 2 Multi-Round Bound & High-Probability Dissemination -/

/-- Numerical upper bound proved directly from Mathlib's `Real.exp_neg_one_lt_d9`:
    `Real.exp (-1/2) < 0.6066`. -/
theorem exp_neg_half_lt_const : Real.exp (-(1 / 2 : ℝ)) < 6066 / 10000 := by
  have h1 : (Real.exp (-(1 / 2 : ℝ))) ^ 2 = Real.exp (-1 : ℝ) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h2 : Real.exp (-1 : ℝ) < 0.3678794412 := Real.exp_neg_one_lt_d9
  have hpos : 0 < Real.exp (-(1 / 2 : ℝ)) := Real.exp_pos _
  nlinarith

/-- Over `R` rounds starting from Phase 2 (`(n : ℝ) / 2 ≤ S.card`), any fixed node `w`
    escapes infection with probability at most `Real.exp (-R / 2)`. -/
theorem prob_runRounds_notMem_le {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ∀ (R : ℕ) (S : Finset (Fin n)), (n : ℝ) / 2 ≤ S.card → ∀ w : Fin n,
      prob (runRounds n R S) (fun S' => w ∉ S') ≤ ENNReal.ofReal (Real.exp (-((R : ℝ) / 2)))
  | 0, S, _, w => by
    rw [runRounds, prob_pure]
    simp only [Nat.cast_zero, zero_div, neg_zero, Real.exp_zero, ENNReal.ofReal_one]
    split_ifs <;> simp
  | R + 1, S, hP2, w => by
    rw [runRounds, prob_bind]
    have hstep : ∀ S1 : Finset (Fin n),
        pushRoundPMF n S S1 * prob (runRounds n R S1) (fun S' => w ∉ S') ≤
          (if w ∉ S1 then pushRoundPMF n S S1 else 0) * ENNReal.ofReal (Real.exp (-((R : ℝ) / 2))) := by
      intro S1
      by_cases hw1 : w ∈ S1
      · have hz : prob (runRounds n R S1) (fun S' => w ∉ S') = 0 := by
          rw [prob]
          refine Finset.sum_eq_zero fun S' _ => ?_
          by_cases hsupp : S' ∈ (runRounds n R S1).support
          · simp [runRounds_support_subset R hsupp hw1]
          · rw [PMF.mem_support_iff, not_not] at hsupp
            split_ifs <;> simp [hsupp]
        simp [hw1, hz]
      · simp only [hw1, not_false_eq_true, ↓reduceIte]
        by_cases hsub : S ⊆ S1
        · have hP2' : (n : ℝ) / 2 ≤ S1.card :=
            le_trans hP2 (Nat.cast_le.mpr (Finset.card_le_card hsub))
          have ih := prob_runRounds_notMem_le hn R S1 hP2' w
          gcongr
        · have hz : pushRoundPMF n S S1 = 0 := by
            by_contra hnz
            have hsupp : S1 ∈ (pushRoundPMF n S).support := by
              rw [PMF.mem_support_iff]; exact hnz
            exact hsub (pushRoundPMF_support_subset hsupp)
          simp [hz]
    have hsum1 : (∑ S1 : Finset (Fin n),
        (if w ∉ S1 then pushRoundPMF n S S1 else 0) * ENNReal.ofReal (Real.exp (-((R : ℝ) / 2)))) =
        prob (pushRoundPMF n S) (fun S1 => w ∉ S1) * ENNReal.ofReal (Real.exp (-((R : ℝ) / 2))) := by
      rw [← Finset.sum_mul, prob]
    have hsingle : prob (pushRoundPMF n S) (fun S1 => w ∉ S1) ≤
        ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ))) := by
      have hreal := probR_pushRound_notMem_le_exp_neg_half hn S hP2 w
      rw [← ENNReal.ofReal_toReal (prob_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal hreal
    have hexp : ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ))) * ENNReal.ofReal (Real.exp (-((R : ℝ) / 2))) =
        ENNReal.ofReal (Real.exp (-(((R + 1 : ℕ) : ℝ) / 2))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      push_cast
      ring
    calc
      ∑ S1 : Finset (Fin n), pushRoundPMF n S S1 * prob (runRounds n R S1) (fun S' => w ∉ S')
          ≤ ∑ S1 : Finset (Fin n),
              (if w ∉ S1 then pushRoundPMF n S S1 else 0) * ENNReal.ofReal (Real.exp (-((R : ℝ) / 2))) :=
        Finset.sum_le_sum fun S1 _ => hstep S1
      _ = prob (pushRoundPMF n S) (fun S1 => w ∉ S1) * ENNReal.ofReal (Real.exp (-((R : ℝ) / 2))) := hsum1
      _ ≤ ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ))) * ENNReal.ofReal (Real.exp (-((R : ℝ) / 2))) := by
        gcongr
      _ = ENNReal.ofReal (Real.exp (-(((R + 1 : ℕ) : ℝ) / 2))) := hexp

/-- Union bound for Phase 2: starting from `(n : ℝ) / 2 ≤ S.card`, after `R` rounds
    the probability that the cluster is NOT fully infected (`S' ≠ Finset.univ`) is at most
    `n * Real.exp (-R / 2)`. -/
theorem probR_runRounds_not_univ_le {n : ℕ} [NeZero n] (hn : 2 ≤ n) (R : ℕ)
    (S : Finset (Fin n)) (hP2 : (n : ℝ) / 2 ≤ S.card) :
    probR (runRounds n R S) (fun S' => S' ≠ Finset.univ) ≤
      (n : ℝ) * Real.exp (-((R : ℝ) / 2)) := by
  have hiff : ∀ S' : Finset (Fin n), S' ≠ Finset.univ → ∃ w ∈ (Finset.univ : Finset (Fin n)), w ∉ S' := by
    intro S' hne
    by_contra hall
    push Not at hall
    apply hne
    ext w
    simp [hall w]
  have h1 : prob (runRounds n R S) (fun S' => S' ≠ Finset.univ) ≤
      prob (runRounds n R S) (fun S' => ∃ w ∈ (Finset.univ : Finset (Fin n)), w ∉ S') :=
    prob_mono _ _ _ hiff
  have h2 : prob (runRounds n R S) (fun S' => ∃ w ∈ (Finset.univ : Finset (Fin n)), w ∉ S') ≤
      ∑ w ∈ (Finset.univ : Finset (Fin n)), prob (runRounds n R S) (fun S' => w ∉ S') :=
    prob_union_le_finset _ _ _
  have h3 : (∑ w ∈ (Finset.univ : Finset (Fin n)), prob (runRounds n R S) (fun S' => w ∉ S')) ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-((R : ℝ) / 2))) := by
    calc
      (∑ w ∈ (Finset.univ : Finset (Fin n)), prob (runRounds n R S) (fun S' => w ∉ S'))
          ≤ ∑ _w ∈ (Finset.univ : Finset (Fin n)), ENNReal.ofReal (Real.exp (-((R : ℝ) / 2))) :=
        Finset.sum_le_sum fun w _ => prob_runRounds_notMem_le hn R S hP2 w
      _ = (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-((R : ℝ) / 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hle : prob (runRounds n R S) (fun S' => S' ≠ Finset.univ) ≤
      ENNReal.ofReal ((n : ℝ) * Real.exp (-((R : ℝ) / 2))) := by
    refine le_trans h1 (le_trans h2 (le_trans h3 ?_))
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  rw [probR]
  calc
    (prob (runRounds n R S) fun S' => S' ≠ Finset.univ).toReal
        ≤ (ENNReal.ofReal ((n : ℝ) * Real.exp (-((R : ℝ) / 2)))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = (n : ℝ) * Real.exp (-((R : ℝ) / 2)) := ENNReal.toReal_ofReal (by positivity)

/-- **Axiom-Free Phase 2 O(log n) Convergence Theorem**:
    Starting from half-saturation (`n / 2 ≤ S.card`), for any confidence parameter `c : ℝ`
    and round count `R ≥ 2 * (c + 1) * Real.log n`, full dissemination succeeds with probability
    at least `1 - (n : ℝ) ^ (-c)`. -/
theorem phase2_convergence_whp {n : ℕ} [NeZero n] (hn : 2 ≤ n) (c : ℝ) (R : ℕ)
    (hR : 2 * (c + 1) * Real.log n ≤ R)
    (S : Finset (Fin n)) (hP2 : (n : ℝ) / 2 ≤ S.card) :
    probR (runRounds n R S) (fun S' => S' ≠ Finset.univ) ≤ (n : ℝ) ^ (-c) := by
  have h1 := probR_runRounds_not_univ_le hn R S hP2
  have hn_pos : (0 : ℝ) < n := by positivity
  have hdiv : -((R : ℝ) / 2) ≤ -((c + 1) * Real.log n) := by linarith
  have hexp : Real.exp (-((R : ℝ) / 2)) ≤ Real.exp (-((c + 1) * Real.log n)) :=
    Real.exp_le_exp.mpr hdiv
  have hmul : (n : ℝ) * Real.exp (-((R : ℝ) / 2)) ≤
      (n : ℝ) * Real.exp (-((c + 1) * Real.log n)) :=
    mul_le_mul_of_nonneg_left hexp hn_pos.le
  have hpow : (n : ℝ) * Real.exp (-((c + 1) * Real.log n)) = (n : ℝ) ^ (-c) := by
    nth_rw 1 [← Real.exp_log hn_pos]
    rw [← Real.exp_add, Real.rpow_def_of_pos hn_pos]
    congr 1
    ring
  exact le_trans h1 (by rw [← hpow]; exact hmul)

end SwimMathlibProofs

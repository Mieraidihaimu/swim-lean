import SwimMathlibProofs.EpidemicPMF

/-!
# Phase 1 Exponential Growth & End-to-End O(log n) Convergence (Zero Axioms)

This module proves Phase 1 of the SWIM push-gossip dissemination theorem in
Mathlib4 (`PMF`), coupling the exact Markov chain `kPicks` / `runRounds` with a
`Binomial(m, 1/2)` lower-bound process and proving a Chernoff lower-tail bound.

Combined with `phase2_convergence_whp` from `EpidemicPMF.lean`, we obtain the
complete end-to-end theorem `full_epidemic_convergence_whp`: starting from a
single infected node `S₀ = {src}`, in `O(log n)` rounds all `n` nodes are
infected with high probability (`≥ 1 - 3 * n ^ (-c)`).
-/

namespace SwimMathlibProofs

open scoped BigOperators ENNReal

/-! ### Binomial(m, 1/2) Reference Process & Chernoff Lower Tail -/

/-- Fair Bernoulli coin (`p = 1/2`). -/
noncomputable def halfBernoulli : PMF Bool :=
  PMF.ofFintype (fun _ => (2 : ℝ≥0∞)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp) (by simp))

@[simp]
theorem halfBernoulli_apply (b : Bool) : halfBernoulli b = (2 : ℝ≥0∞)⁻¹ := rfl

/-- One `Bernoulli(1/2)` increment step on `ℕ`. -/
noncomputable def binomHalfStep (k : ℕ) : PMF ℕ :=
  halfBernoulli.bind fun b => PMF.pure (if b then k + 1 else k)

/-- `Binomial(m, 1/2)` distribution over `ℕ`. -/
noncomputable def binomHalfPMF : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | m + 1 => (binomHalfPMF m).bind binomHalfStep

theorem binomHalfPMF_support_le : ∀ (m k : ℕ), k ∈ (binomHalfPMF m).support → k ≤ m
  | 0, k, h => by
    rw [binomHalfPMF, PMF.mem_support_pure_iff] at h
    omega
  | m + 1, k, h => by
    rw [binomHalfPMF, PMF.mem_support_bind_iff] at h
    rcases h with ⟨k0, hk0, hstep⟩
    have hk0_le := binomHalfPMF_support_le m k0 hk0
    rw [binomHalfStep, PMF.mem_support_bind_iff] at hstep
    rcases hstep with ⟨b, _, hb⟩
    rw [PMF.mem_support_pure_iff] at hb
    cases b with
    | false => simp_all; omega
    | true => simp_all

/-- Probability of a decidable predicate on `ℕ` under a `PMF ℕ` supported on `[0, bound]`. -/
noncomputable def probNatBounded (p : PMF ℕ) (bound : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (bound + 1), if P k then p k else 0

noncomputable def probNatR (p : PMF ℕ) (bound : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℝ :=
  (probNatBounded p bound P).toReal

theorem probNatBounded_eq_tsum (p : PMF ℕ) (bound : ℕ) (hsupp : ∀ k, k ∈ p.support → k ≤ bound)
    (P : ℕ → Prop) [DecidablePred P] :
    probNatBounded p bound P = ∑' k : ℕ, if P k then p k else 0 := by
  rw [probNatBounded]
  symm
  refine tsum_eq_sum fun k hk => ?_
  rw [Finset.mem_range, not_lt] at hk
  have hzero : p k = 0 := by
    by_contra hnz
    have hmem : k ∈ p.support := by rw [PMF.mem_support_iff]; exact hnz
    have := hsupp k hmem
    omega
  simp [hzero]

theorem probNatBounded_le_one (p : PMF ℕ) (bound : ℕ) (_hsupp : ∀ k, k ∈ p.support → k ≤ bound)
    (P : ℕ → Prop) [DecidablePred P] :
    probNatBounded p bound P ≤ 1 := by
  calc
    probNatBounded p bound P
        = ∑ k ∈ Finset.range (bound + 1), if P k then p k else 0 := rfl
    _ ≤ ∑ k ∈ Finset.range (bound + 1), p k := by
      refine Finset.sum_le_sum fun k _ => ?_
      split_ifs <;> simp
    _ ≤ ∑' k : ℕ, p k := sum_le_tsum _
    _ = 1 := p.tsum_coe

theorem probNatBounded_ne_top (p : PMF ℕ) (bound : ℕ) (hsupp : ∀ k, k ∈ p.support → k ≤ bound)
    (P : ℕ → Prop) [DecidablePred P] :
    probNatBounded p bound P ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (probNatBounded_le_one p bound hsupp P)

/-- Moment Generating Function at `θ = -1`: `E[exp(-X)]` for `X ~ Binomial(m, 1/2)`. -/
noncomputable def binomHalfMGF (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), (binomHalfPMF m k).toReal * Real.exp (-(k : ℝ))

theorem binomHalfStep_apply_sum (f : ℕ → ℝ) (k : ℕ) :
    ∑' j : ℕ, (binomHalfStep k j).toReal * f j =
      (1 / 2 : ℝ) * f (k + 1) + (1 / 2 : ℝ) * f k := by
  have hsupp : ∀ j : ℕ, j ∉ ({k, k + 1} : Finset ℕ) → (binomHalfStep k j) = 0 := by
    intro j hj
    by_contra hnz
    have hmem : j ∈ (binomHalfStep k).support := by rw [PMF.mem_support_iff]; exact hnz
    rw [binomHalfStep, PMF.mem_support_bind_iff] at hmem
    rcases hmem with ⟨b, _, hb⟩
    rw [PMF.mem_support_pure_iff] at hb
    cases b with
    | false => simp_all
    | true => simp_all
  have htsum : (∑' j : ℕ, (binomHalfStep k j).toReal * f j) =
      ∑ j ∈ ({k, k + 1} : Finset ℕ), (binomHalfStep k j).toReal * f j := by
    refine tsum_eq_sum fun j hj => ?_
    simp [hsupp j hj]
  rw [htsum, Finset.sum_pair (by omega : k ≠ k + 1)]
  have hk0 : binomHalfStep k k = (2 : ℝ≥0∞)⁻¹ := by
    rw [binomHalfStep, PMF.bind_apply]
    rw [tsum_eq_sum (s := ({false, true} : Finset Bool)) (fun b hb => by cases b <;> simp at hb)]
    rw [Finset.sum_pair (by decide)]
    simp [PMF.pure_apply]
  have hk1 : binomHalfStep k (k + 1) = (2 : ℝ≥0∞)⁻¹ := by
    rw [binomHalfStep, PMF.bind_apply]
    rw [tsum_eq_sum (s := ({false, true} : Finset Bool)) (fun b hb => by cases b <;> simp at hb)]
    rw [Finset.sum_pair (by decide)]
    simp [PMF.pure_apply]
  rw [hk0, hk1]
  have hhalf : ((2 : ℝ≥0∞)⁻¹).toReal = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]
  ring

theorem binomHalfMGF_eq (m : ℕ) :
    binomHalfMGF m = ((1 / 2 : ℝ) * Real.exp (-1) + 1 / 2) ^ m := by
  induction m with
  | zero =>
    simp [binomHalfMGF, binomHalfPMF, PMF.pure_apply]
  | succ m ih =>
    rw [binomHalfMGF]
    have hbind : ∀ k : ℕ, (binomHalfPMF (m + 1) k).toReal =
        ∑ j ∈ Finset.range (m + 1), (binomHalfPMF m j).toReal * (binomHalfStep j k).toReal := by
      intro k
      rw [binomHalfPMF, PMF.bind_apply]
      have hsum_range : (∑' j : ℕ, binomHalfPMF m j * binomHalfStep j k) =
          ∑ j ∈ Finset.range (m + 1), binomHalfPMF m j * binomHalfStep j k := by
        refine tsum_eq_sum fun j hj => ?_
        rw [Finset.mem_range, not_lt] at hj
        have hz : binomHalfPMF m j = 0 := by
          by_contra hnz
          have := binomHalfPMF_support_le m j (by rw [PMF.mem_support_iff]; exact hnz)
          omega
        simp [hz]
      rw [hsum_range, ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl fun j _ => ENNReal.toReal_mul
      · intro j _
        exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
    have hswap : (∑ k ∈ Finset.range (m + 1 + 1), (binomHalfPMF (m + 1) k).toReal * Real.exp (-(k : ℝ))) =
        ∑ j ∈ Finset.range (m + 1),
          (binomHalfPMF m j).toReal *
            (∑ k ∈ Finset.range (m + 1 + 1), (binomHalfStep j k).toReal * Real.exp (-(k : ℝ))) := by
      simp_rw [hbind, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hswap]
    have hstep_exp : ∀ j ∈ Finset.range (m + 1),
        (∑ k ∈ Finset.range (m + 1 + 1), (binomHalfStep j k).toReal * Real.exp (-(k : ℝ))) =
          ((1 / 2 : ℝ) * Real.exp (-1) + 1 / 2) * Real.exp (-(j : ℝ)) := by
      intro j hj
      have hj_lt : j < m + 1 := Finset.mem_range.mp hj
      have htsum_eq : (∑ k ∈ Finset.range (m + 1 + 1), (binomHalfStep j k).toReal * Real.exp (-(k : ℝ))) =
          ∑' k : ℕ, (binomHalfStep j k).toReal * Real.exp (-(k : ℝ)) := by
        symm
        refine tsum_eq_sum fun k hk => ?_
        rw [Finset.mem_range, not_lt] at hk
        have hstep_z : binomHalfStep j k = 0 := by
          by_contra hnz
          have hmem : k ∈ (binomHalfStep j).support := by rw [PMF.mem_support_iff]; exact hnz
          rw [binomHalfStep, PMF.mem_support_bind_iff] at hmem
          rcases hmem with ⟨b, _, hb⟩
          rw [PMF.mem_support_pure_iff] at hb
          cases b with
          | false => simp_all; omega
          | true => simp_all; omega
        simp [hstep_z]
      rw [htsum_eq, binomHalfStep_apply_sum (fun k => Real.exp (-(k : ℝ))) j]
      have hexp1 : Real.exp (-((j + 1 : ℕ) : ℝ)) = Real.exp (-1) * Real.exp (-(j : ℝ)) := by
        rw [← Real.exp_add]
        congr 1; push_cast; ring
      rw [hexp1]
      ring
    have hcongr : (∑ j ∈ Finset.range (m + 1),
        (binomHalfPMF m j).toReal *
          (∑ k ∈ Finset.range (m + 1 + 1), (binomHalfStep j k).toReal * Real.exp (-(k : ℝ)))) =
        ((1 / 2 : ℝ) * Real.exp (-1) + 1 / 2) * binomHalfMGF m := by
      rw [binomHalfMGF, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hstep_exp j hj]
      ring
    rw [hcongr, ih, pow_succ]
    ring

/-- **Chernoff Bound for Binomial(m, 1/2)**:
    `P[X ≤ a] ≤ exp(a) * (1/2 * exp(-1) + 1/2)^m`. -/
theorem binomHalf_chernoff_le (m : ℕ) (a : ℝ) :
    probNatR (binomHalfPMF m) m (fun k => (k : ℝ) ≤ a) ≤
      Real.exp a * ((1 / 2 : ℝ) * Real.exp (-1) + 1 / 2) ^ m := by
  rw [probNatR, probNatBounded, ENNReal.toReal_sum]
  · calc
      ∑ k ∈ Finset.range (m + 1), (if (k : ℝ) ≤ a then binomHalfPMF m k else 0).toReal
          ≤ ∑ k ∈ Finset.range (m + 1),
              Real.exp a * ((binomHalfPMF m k).toReal * Real.exp (-(k : ℝ))) := by
        refine Finset.sum_le_sum fun k _ => ?_
        split_ifs with hk
        · have h1 : (1 : ℝ) ≤ Real.exp a * Real.exp (-(k : ℝ)) := by
            rw [← Real.exp_add]
            exact Real.one_le_exp (by linarith)
          have hnn : 0 ≤ (binomHalfPMF m k).toReal := ENNReal.toReal_nonneg
          nlinarith
        · simp only [ENNReal.toReal_zero]
          positivity
      _ = Real.exp a * binomHalfMGF m := by
        rw [← Finset.mul_sum, binomHalfMGF]
      _ = Real.exp a * ((1 / 2 : ℝ) * Real.exp (-1) + 1 / 2) ^ m := by
        rw [binomHalfMGF_eq]
  · intro k _
    split_ifs <;> simp [PMF.apply_ne_top]

/-- Numeric Chernoff contraction proved directly from Mathlib's `exp_one_lt_d9` & `exp_neg_one_lt_d9`:
    `exp(1/4) * (1/2 * exp(-1) + 1/2) ≤ exp(-1/8)`. -/
theorem chernoff_quarter_factor_le :
    Real.exp (1 / 4 : ℝ) * ((1 / 2 : ℝ) * Real.exp (-1) + 1 / 2) ≤ Real.exp (-(1 / 8 : ℝ)) := by
  have h_e : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h_em1 : Real.exp (-1) < 0.3678794412 := Real.exp_neg_one_lt_d9
  have h_e_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have h_em1_pos : 0 < Real.exp (-1) := Real.exp_pos (-1)
  set A := Real.exp (1 / 4 : ℝ) * ((1 / 2 : ℝ) * Real.exp (-1) + 1 / 2)
  have hA_pos : 0 < A := by positivity
  have hA4 : A ^ 4 = Real.exp 1 * ((1 / 2 : ℝ) * Real.exp (-1) + 1 / 2) ^ 4 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2; norm_num
  have hpow4 : ((1 / 2 : ℝ) * Real.exp (-1) + 1 / 2) ^ 4 < (0.68394 : ℝ) ^ 4 := by
    gcongr
    linarith
  have hA_lt : A < 0.88 := by
    have h4 : A ^ 4 < (0.88 : ℝ) ^ 4 := by
      rw [hA4]
      calc
        Real.exp 1 * ((1 / 2 : ℝ) * Real.exp (-1) + 1 / 2) ^ 4
            < 2.7182818286 * (0.68394 : ℝ) ^ 4 := by gcongr
        _ < (0.88 : ℝ) ^ 4 := by norm_num
    exact (pow_lt_pow_iff_left₀ hA_pos.le (by norm_num) (by norm_num : 4 ≠ 0)).mp h4
  have h_inv : (0.88 : ℝ) < Real.exp (-(1 / 8 : ℝ)) := by
    have hexp8 : (Real.exp (-(1 / 8 : ℝ))) ^ 8 = Real.exp (-1) := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num
    have h_em1_gt : (0.88 : ℝ) ^ 8 < Real.exp (-1) := by
      have hmul : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
      have h1 : (0.88 : ℝ) ^ 8 * 2.7182818286 < 1 := by norm_num
      nlinarith
    have h8 : (0.88 : ℝ) ^ 8 < (Real.exp (-(1 / 8 : ℝ))) ^ 8 := by rwa [hexp8]
    exact (pow_lt_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num : 8 ≠ 0)).mp h8
  linarith

/-- **Quarter-Growth Exponential Tail**:
    `P[X ≤ m / 4] ≤ exp(-m / 8)` for `X ~ Binomial(m, 1/2)`. -/
theorem binomHalf_quarter_tail_le (m : ℕ) :
    probNatR (binomHalfPMF m) m (fun k => (k : ℝ) ≤ (m : ℝ) / 4) ≤ Real.exp (-((m : ℝ) / 8)) := by
  have h1 := binomHalf_chernoff_le m ((m : ℝ) / 4)
  have hexp_pow : Real.exp ((m : ℝ) / 4) = (Real.exp (1 / 4 : ℝ)) ^ m := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hfactor := chernoff_quarter_factor_le
  have hpow : (Real.exp (1 / 4 : ℝ) * ((1 / 2 : ℝ) * Real.exp (-1) + 1 / 2)) ^ m ≤
      (Real.exp (-(1 / 8 : ℝ))) ^ m :=
    pow_le_pow_left₀ (by positivity) hfactor m
  have hexp_rhs : (Real.exp (-(1 / 8 : ℝ))) ^ m = Real.exp (-((m : ℝ) / 8)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hexp_pow, ← mul_pow] at h1
  rw [hexp_rhs] at hpow
  exact le_trans h1 hpow

/-! ### Coupling `kPicks` and `runRounds` to `Binomial(m, 1/2)` -/

theorem kPicks_succ {n : ℕ} [NeZero n] (k : ℕ) (S : Finset (Fin n)) :
    kPicks n (k + 1) S = (uniformNode n).bind fun v => kPicks n k (insert v S) := by
  rw [kPicks, pickOne, PMF.bind_bind]
  congr 1
  ext v
  rw [PMF.pure_bind]

theorem probNatBounded_bind_step {P : ℕ → Prop} [DecidablePred P] (k : ℕ) :
    probNatR (binomHalfPMF (k + 1)) (k + 1) P =
      (1 / 2 : ℝ) * probNatR (binomHalfPMF k) k (fun x => P (x + 1)) +
      (1 / 2 : ℝ) * probNatR (binomHalfPMF k) k P := by
  rw [probNatR, probNatR, probNatR]
  rw [probNatBounded_eq_tsum _ _ (binomHalfPMF_support_le (k + 1))]
  rw [probNatBounded_eq_tsum _ _ (binomHalfPMF_support_le k)]
  rw [probNatBounded_eq_tsum _ _ (binomHalfPMF_support_le k)]
  have h1 : (∑' m : ℕ, if P m then binomHalfPMF (k + 1) m else 0) =
      ∑' j : ℕ, binomHalfPMF k j *
        ((2 : ℝ≥0∞)⁻¹ * (if P (j + 1) then 1 else 0) + (2 : ℝ≥0∞)⁻¹ * (if P j then 1 else 0)) := by
    have hs : ∀ m : ℕ, (if P m then binomHalfPMF (k + 1) m else 0) =
        ∑' j : ℕ, binomHalfPMF k j * (if P m then binomHalfStep j m else 0) := by
      intro m
      rw [binomHalfPMF, PMF.bind_apply]
      split_ifs with hPm
      · rfl
      · simp
    simp_rw [hs]
    rw [tsum_comm]
    refine tsum_congr fun j => ?_
    rw [ENNReal.tsum_mul_left]
    congr 1
    rw [tsum_eq_sum (s := ({j, j + 1} : Finset ℕ)) fun m hm => by
      have hz : binomHalfStep j m = 0 := by
        by_contra hnz
        have hmem : m ∈ (binomHalfStep j).support := by rw [PMF.mem_support_iff]; exact hnz
        rw [binomHalfStep, PMF.mem_support_bind_iff] at hmem
        rcases hmem with ⟨b, _, hb⟩
        rw [PMF.mem_support_pure_iff] at hb
        cases b with
        | false => simp_all
        | true => simp_all
      split_ifs <;> simp [hz]]
    rw [Finset.sum_pair (by omega : j ≠ j + 1)]
    have hk0 : binomHalfStep j j = (2 : ℝ≥0∞)⁻¹ := by
      rw [binomHalfStep, PMF.bind_apply]
      rw [tsum_eq_sum (s := ({false, true} : Finset Bool)) (fun b hb => by cases b <;> simp at hb)]
      rw [Finset.sum_pair (by decide)]; simp [PMF.pure_apply]
    have hk1 : binomHalfStep j (j + 1) = (2 : ℝ≥0∞)⁻¹ := by
      rw [binomHalfStep, PMF.bind_apply]
      rw [tsum_eq_sum (s := ({false, true} : Finset Bool)) (fun b hb => by cases b <;> simp at hb)]
      rw [Finset.sum_pair (by decide)]; simp [PMF.pure_apply]
    rw [hk0, hk1]
    split_ifs <;> ring
  rw [h1]
  have hsplit : (∑' j : ℕ, binomHalfPMF k j *
      ((2 : ℝ≥0∞)⁻¹ * (if P (j + 1) then 1 else 0) + (2 : ℝ≥0∞)⁻¹ * (if P j then 1 else 0))) =
      (2 : ℝ≥0∞)⁻¹ * (∑' j : ℕ, if P (j + 1) then binomHalfPMF k j else 0) +
      (2 : ℝ≥0∞)⁻¹ * (∑' j : ℕ, if P j then binomHalfPMF k j else 0) := by
    have hmul : ∀ j : ℕ, binomHalfPMF k j *
        ((2 : ℝ≥0∞)⁻¹ * (if P (j + 1) then 1 else 0) + (2 : ℝ≥0∞)⁻¹ * (if P j then 1 else 0)) =
        (2 : ℝ≥0∞)⁻¹ * (if P (j + 1) then binomHalfPMF k j else 0) +
        (2 : ℝ≥0∞)⁻¹ * (if P j then binomHalfPMF k j else 0) := by
      intro j; split_ifs <;> ring
    simp_rw [hmul, ENNReal.tsum_add, ENNReal.tsum_mul_left]
  rw [hsplit]
  have hfin1 : (2 : ℝ≥0∞)⁻¹ * (∑' j : ℕ, if P (j + 1) then binomHalfPMF k j else 0) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (by simp) ?_
    rw [← probNatBounded_eq_tsum _ _ (binomHalfPMF_support_le k)]
    exact probNatBounded_ne_top _ _ (binomHalfPMF_support_le k) _
  have hfin2 : (2 : ℝ≥0∞)⁻¹ * (∑' j : ℕ, if P j then binomHalfPMF k j else 0) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (by simp) ?_
    rw [← probNatBounded_eq_tsum _ _ (binomHalfPMF_support_le k)]
    exact probNatBounded_ne_top _ _ (binomHalfPMF_support_le k) _
  rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hhalf : ((2 : ℝ≥0∞)⁻¹).toReal = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]

theorem probNatR_mono (p : PMF ℕ) (bound : ℕ) (hsupp : ∀ k, k ∈ p.support → k ≤ bound)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ k, P k → Q k) :
    probNatR p bound P ≤ probNatR p bound Q := by
  rw [probNatR, probNatR]
  refine ENNReal.toReal_mono (probNatBounded_ne_top p bound hsupp Q) ?_
  refine Finset.sum_le_sum fun k _ => ?_
  split_ifs with hP hQ
  · exact le_rfl
  · exact False.elim (hQ (hPQ k hP))
  · simp
  · exact le_rfl

/-- **Stochastic Dominance for `kPicks`**:
    As long as target threshold `T ≤ (n + 1) / 2` (so any set with `< T` infected nodes
    satisfies `2 * S.card < n`, meaning hit probability `≥ 1/2`), `kPicks n k S`
    stochastically dominates `S.card + Binomial(k, 1/2)`. -/
theorem probR_kPicks_card_lt_le_binom {n : ℕ} [NeZero n] (hn : 2 ≤ n) (T : ℕ)
    (hT : T ≤ (n + 1) / 2) :
    ∀ (k : ℕ) (S : Finset (Fin n)),
      probR (kPicks n k S) (fun S' => S'.card < T) ≤
        probNatR (binomHalfPMF k) k (fun x => S.card + x < T)
  | 0, S => by
    rw [kPicks, probR, prob_pure, probNatR, probNatBounded, Finset.range_one, Finset.sum_singleton]
    simp only [binomHalfPMF, PMF.pure_apply, ↓reduceIte, Nat.add_zero]
    split_ifs <;> simp
  | k + 1, S => by
    by_cases hreach : T ≤ S.card
    · have hz : prob (kPicks n (k + 1) S) (fun S' => S'.card < T) = 0 := by
        rw [prob]
        refine Finset.sum_eq_zero fun S' _ => ?_
        by_cases hsupp : S' ∈ (kPicks n (k + 1) S).support
        · have hcard : T ≤ S'.card := le_trans hreach (Finset.card_le_card (kPicks_support_subset _ hsupp))
          simp [not_lt.mpr hcard]
        · rw [PMF.mem_support_iff, not_not] at hsupp
          split_ifs <;> simp [hsupp]
      rw [probR, hz, ENNReal.toReal_zero, probNatR]
      exact ENNReal.toReal_nonneg
    · have hS_lt : S.card < T := Nat.lt_of_not_le hreach
      have h2S : 2 * S.card < n := by omega
      have hS_le_n : S.card ≤ n := by omega
      rw [kPicks_succ, probR, prob_bind]
      have hsum : (∑ v : Fin n, uniformNode n v * prob (kPicks n k (insert v S)) (fun S' => S'.card < T)).toReal =
          ∑ v : Fin n, (n : ℝ)⁻¹ * probR (kPicks n k (insert v S)) (fun S' => S'.card < T) := by
        rw [ENNReal.toReal_sum (fun v _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (prob_ne_top _ _))]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [ENNReal.toReal_mul, uniformNode_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, probR]
      rw [hsum]
      set A := probNatR (binomHalfPMF k) k (fun x => S.card + 1 + x < T)
      set B := probNatR (binomHalfPMF k) k (fun x => S.card + x < T)
      have hAB : A ≤ B := probNatR_mono (binomHalfPMF k) k (binomHalfPMF_support_le k) _ _ (fun x hx => by omega)
      have hterm : ∀ v : Fin n,
          (n : ℝ)⁻¹ * probR (kPicks n k (insert v S)) (fun S' => S'.card < T) ≤
            if v ∈ S then (n : ℝ)⁻¹ * B else (n : ℝ)⁻¹ * A := by
        intro v
        have hn_nn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
        split_ifs with hv
        · rw [Finset.insert_eq_of_mem hv]
          exact mul_le_mul_of_nonneg_left (probR_kPicks_card_lt_le_binom hn T hT k S) hn_nn
        · have ih := probR_kPicks_card_lt_le_binom hn T hT k (insert v S)
          rw [Finset.card_insert_of_notMem hv] at ih
          exact mul_le_mul_of_nonneg_left ih hn_nn
      have hsplit_sum : (∑ v : Fin n, if v ∈ S then (n : ℝ)⁻¹ * B else (n : ℝ)⁻¹ * A) =
          ((S.card : ℝ) / n) * B + (((n - S.card : ℕ) : ℝ) / n) * A := by
        rw [← Finset.sum_add_sum_compl S (fun v : Fin n => if v ∈ S then (n : ℝ)⁻¹ * B else (n : ℝ)⁻¹ * A)]
        have h1 : ∑ v ∈ S, (if v ∈ S then (n : ℝ)⁻¹ * B else (n : ℝ)⁻¹ * A) = ((S.card : ℝ) / n) * B := by
          trans ∑ _v ∈ S, (n : ℝ)⁻¹ * B
          · refine Finset.sum_congr rfl fun v hv => if_pos hv
          · rw [Finset.sum_const, nsmul_eq_mul]; ring
        have h2 : ∑ v ∈ Sᶜ, (if v ∈ S then (n : ℝ)⁻¹ * B else (n : ℝ)⁻¹ * A) = (((n - S.card : ℕ) : ℝ) / n) * A := by
          trans ∑ _v ∈ Sᶜ, (n : ℝ)⁻¹ * A
          · refine Finset.sum_congr rfl fun v hv => if_neg (Finset.mem_compl.mp hv)
          · rw [Finset.sum_const, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul]; ring
        rw [h1, h2]
      have hprob_step : probNatR (binomHalfPMF (k + 1)) (k + 1) (fun x => S.card + x < T) =
          (1 / 2 : ℝ) * A + (1 / 2 : ℝ) * B := by
        have h := probNatBounded_bind_step (P := fun x => S.card + x < T) k
        have h' : probNatR (binomHalfPMF k) k (fun x => S.card + (x + 1) < T) = A := by
          dsimp [A]; congr 1; ext x; congr 1; omega
        rw [h'] at h
        simpa [B] using h
      rw [hprob_step]
      have hn_pos : (0 : ℝ) < n := by positivity
      have hp_ge : (1 / 2 : ℝ) ≤ ((n - S.card : ℕ) : ℝ) / n := by
        rw [le_div_iff₀ hn_pos]
        have hcast : ((n - S.card : ℕ) : ℝ) = (n : ℝ) - S.card := by
          have : (n - S.card) + S.card = n := Nat.sub_add_cancel hS_le_n
          have : ((n - S.card : ℕ) : ℝ) + S.card = n := by exact_mod_cast this
          linarith
        rw [hcast]
        have h2S_r : 2 * (S.card : ℝ) ≤ n := by exact_mod_cast h2S.le
        linarith
      have hp_sum : ((S.card : ℝ) / n) + (((n - S.card : ℕ) : ℝ) / n) = 1 := by
        have hcast : ((n - S.card : ℕ) : ℝ) = (n : ℝ) - S.card := by
          have : (n - S.card) + S.card = n := Nat.sub_add_cancel hS_le_n
          have : ((n - S.card : ℕ) : ℝ) + S.card = n := by exact_mod_cast this
          linarith
        rw [hcast]
        field_simp
        ring
      have hcomb : ((S.card : ℝ) / n) * B + (((n - S.card : ℕ) : ℝ) / n) * A ≤
          (1 / 2 : ℝ) * A + (1 / 2 : ℝ) * B := by
        rw [show (S.card : ℝ) / n = 1 - ((n - S.card : ℕ) : ℝ) / n by linarith]
        nlinarith
      exact le_trans (Finset.sum_le_sum fun v _ => hterm v) (by rw [hsplit_sum]; exact hcomb)

/-- One synchronous push-gossip round from `S` (with `1 ≤ S.card`) grows by at least 1
    with probability `≥ 1/2` whenever `S.card < (n + 1) / 2`. -/
theorem probR_pushRound_no_growth_le_half {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (S : Finset (Fin n)) (h1 : 1 ≤ S.card) (hlt : S.card < (n + 1) / 2) :
    probR (pushRoundPMF n S) (fun S' => S'.card < S.card + 1) ≤ (1 / 2 : ℝ) := by
  have hT : S.card + 1 ≤ (n + 1) / 2 := hlt
  have hdom := probR_kPicks_card_lt_le_binom hn (S.card + 1) hT S.card S
  rw [pushRoundPMF]
  have hbin : probNatR (binomHalfPMF S.card) S.card (fun x => S.card + x < S.card + 1) ≤ (1 / 2 : ℝ) := by
    have hle : probNatR (binomHalfPMF S.card) S.card (fun x => S.card + x < S.card + 1) ≤
        probNatR (binomHalfPMF S.card) S.card (fun x => x = 0) :=
      probNatR_mono (binomHalfPMF S.card) S.card (binomHalfPMF_support_le S.card) _ _ (fun x hx => by omega)
    have h0 : ∀ m : ℕ, 1 ≤ m → probNatR (binomHalfPMF m) m (fun x => x = 0) ≤ (1 / 2 : ℝ) := by
      intro m hm
      cases m with
      | zero => omega
      | succ m' =>
        have hstep := probNatBounded_bind_step (P := fun x => x = 0) m'
        have hz : probNatR (binomHalfPMF m') m' (fun x => x + 1 = 0) = 0 := by
          rw [probNatR, probNatBounded]
          simp
        rw [hstep, hz]
        have hle1 := probNatBounded_le_one (binomHalfPMF m') m' (binomHalfPMF_support_le m') (fun x => x = 0)
        have hle1_r : probNatR (binomHalfPMF m') m' (fun x => x = 0) ≤ 1 := by
          rw [probNatR, ← ENNReal.toReal_one]
          exact ENNReal.toReal_mono ENNReal.one_ne_top hle1
        linarith
    exact le_trans hle (h0 S.card h1)
  exact le_trans hdom hbin

/-! ### Stage 1a: Warm-up from 1 to `K = O(log n)` -/

theorem pushRound_support_card_ge {n : ℕ} [NeZero n] {S S' : Finset (Fin n)}
    (h : S' ∈ (pushRoundPMF n S).support) : S.card ≤ S'.card :=
  Finset.card_le_card (pushRoundPMF_support_subset h)

theorem probR_runRounds_lt_le_binom {n : ℕ} [NeZero n] (hn : 2 ≤ n) (T : ℕ)
    (hT : T ≤ (n + 1) / 2) :
    ∀ (R : ℕ) (S : Finset (Fin n)), 1 ≤ S.card →
      probR (runRounds n R S) (fun S' => S'.card < T) ≤
        probNatR (binomHalfPMF R) R (fun x => S.card + x < T)
  | 0, S, _ => by
    rw [runRounds, probR, prob_pure, probNatR, probNatBounded, Finset.range_one, Finset.sum_singleton]
    simp only [binomHalfPMF, PMF.pure_apply, ↓reduceIte, Nat.add_zero]
    split_ifs <;> simp
  | R + 1, S, h1 => by
    by_cases hreach : T ≤ S.card
    · have hz : prob (runRounds n (R + 1) S) (fun S' => S'.card < T) = 0 := by
        rw [prob]
        refine Finset.sum_eq_zero fun S' _ => ?_
        by_cases hsupp : S' ∈ (runRounds n (R + 1) S).support
        · have hc : T ≤ S'.card := le_trans hreach (Finset.card_le_card (runRounds_support_subset _ hsupp))
          simp [not_lt.mpr hc]
        · rw [PMF.mem_support_iff, not_not] at hsupp
          split_ifs <;> simp [hsupp]
      rw [probR, hz, ENNReal.toReal_zero, probNatR]
      exact ENNReal.toReal_nonneg
    · have hS_lt : S.card < T := Nat.lt_of_not_le hreach
      have hS_lt_half : S.card < (n + 1) / 2 := lt_of_lt_of_le hS_lt hT
      rw [runRounds, probR, prob_bind]
      have hsum : (∑ S1 : Finset (Fin n), pushRoundPMF n S S1 * prob (runRounds n R S1) (fun S' => S'.card < T)).toReal =
          ∑ S1 : Finset (Fin n), (pushRoundPMF n S S1).toReal * probR (runRounds n R S1) (fun S' => S'.card < T) := by
        rw [ENNReal.toReal_sum (fun S1 _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (prob_ne_top _ _))]
        refine Finset.sum_congr rfl fun S1 _ => ?_
        rw [ENNReal.toReal_mul, probR]
      rw [hsum]
      set A := probNatR (binomHalfPMF R) R (fun x => S.card + 1 + x < T)
      set B := probNatR (binomHalfPMF R) R (fun x => S.card + x < T)
      have hAB : A ≤ B := probNatR_mono (binomHalfPMF R) R (binomHalfPMF_support_le R) _ _ (fun x hx => by omega)
      have hterm : ∀ S1 : Finset (Fin n),
          (pushRoundPMF n S S1).toReal * probR (runRounds n R S1) (fun S' => S'.card < T) ≤
            if S.card + 1 ≤ S1.card then (pushRoundPMF n S S1).toReal * A
            else if S.card ≤ S1.card then (pushRoundPMF n S S1).toReal * B else 0 := by
        intro S1
        by_cases hsupp : S1 ∈ (pushRoundPMF n S).support
        · have hge : S.card ≤ S1.card := pushRound_support_card_ge hsupp
          have h1' : 1 ≤ S1.card := le_trans h1 hge
          have ih := probR_runRounds_lt_le_binom hn T hT R S1 h1'
          by_cases hinc : S.card + 1 ≤ S1.card
          · rw [if_pos hinc]
            have hleA : probNatR (binomHalfPMF R) R (fun x => S1.card + x < T) ≤ A :=
              probNatR_mono (binomHalfPMF R) R (binomHalfPMF_support_le R) _ _ (fun x hx => by omega)
            exact mul_le_mul_of_nonneg_left (le_trans ih hleA) ENNReal.toReal_nonneg
          · rw [if_neg hinc, if_pos hge]
            have hleB : probNatR (binomHalfPMF R) R (fun x => S1.card + x < T) ≤ B :=
              probNatR_mono (binomHalfPMF R) R (binomHalfPMF_support_le R) _ _ (fun x hx => by omega)
            exact mul_le_mul_of_nonneg_left (le_trans ih hleB) ENNReal.toReal_nonneg
        · rw [PMF.mem_support_iff, not_not] at hsupp
          simp [hsupp]
      have hsum_split : (∑ S1 : Finset (Fin n),
          if S.card + 1 ≤ S1.card then (pushRoundPMF n S S1).toReal * A
          else if S.card ≤ S1.card then (pushRoundPMF n S S1).toReal * B else 0) =
          probR (pushRoundPMF n S) (fun S1 => S.card + 1 ≤ S1.card) * A +
          probR (pushRoundPMF n S) (fun S1 => S1.card < S.card + 1) * B := by
        have hsum_grow : (∑ S1 : Finset (Fin n),
            if S.card + 1 ≤ S1.card then (pushRoundPMF n S S1).toReal * A else 0) =
            probR (pushRoundPMF n S) (fun S1 => S.card + 1 ≤ S1.card) * A := by
          rw [probR, prob, ENNReal.toReal_sum (fun _ _ => by split_ifs <;> simp [PMF.apply_ne_top])]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun S1 _ => ?_
          split_ifs <;> simp
        have hsum_stay : (∑ S1 : Finset (Fin n),
            if ¬(S.card + 1 ≤ S1.card) ∧ S.card ≤ S1.card then (pushRoundPMF n S S1).toReal * B else 0) =
            probR (pushRoundPMF n S) (fun S1 => S1.card < S.card + 1) * B := by
          rw [probR, prob, ENNReal.toReal_sum (fun _ _ => by split_ifs <;> simp [PMF.apply_ne_top])]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun S1 _ => ?_
          by_cases hsupp : S1 ∈ (pushRoundPMF n S).support
          · have hge : S.card ≤ S1.card := pushRound_support_card_ge hsupp
            by_cases hinc : S.card + 1 ≤ S1.card
            · simp [hinc, show ¬(S1.card < S.card + 1) by omega]
            · simp [hinc, hge, show S1.card < S.card + 1 by omega]
          · rw [PMF.mem_support_iff, not_not] at hsupp
            split_ifs <;> simp [hsupp]
        rw [← hsum_grow, ← hsum_stay, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun S1 _ => ?_
        by_cases hinc : S.card + 1 ≤ S1.card
        · simp [hinc]
        · by_cases hge : S.card ≤ S1.card
          · simp [hinc, hge]
          · simp [hinc, hge]
      have htot : probR (pushRoundPMF n S) (fun S1 => S.card + 1 ≤ S1.card) +
          probR (pushRoundPMF n S) (fun S1 => S1.card < S.card + 1) = 1 := by
        rw [probR, probR, ← ENNReal.toReal_add (prob_ne_top _ _) (prob_ne_top _ _),
          prob, prob, ← Finset.sum_add_distrib]
        have hsum1 : (∑ S1 : Finset (Fin n),
            ((if S.card + 1 ≤ S1.card then pushRoundPMF n S S1 else 0) +
             (if S1.card < S.card + 1 then pushRoundPMF n S S1 else 0))) =
            ∑ S1 : Finset (Fin n), pushRoundPMF n S S1 := by
          refine Finset.sum_congr rfl fun S1 _ => ?_
          by_cases hinc : S.card + 1 ≤ S1.card
          · simp [hinc, show ¬(S1.card < S.card + 1) by omega]
          · simp [hinc, show S1.card < S.card + 1 by omega]
        have hts : (∑ S1 : Finset (Fin n), pushRoundPMF n S S1) = 1 := by
          calc
            ∑ S1 : Finset (Fin n), pushRoundPMF n S S1
                = ∑' S1 : Finset (Fin n), pushRoundPMF n S S1 := (tsum_fintype _).symm
            _ = 1 := (pushRoundPMF n S).tsum_coe
        rw [hsum1, hts, ENNReal.toReal_one]
      have hstay_le : probR (pushRoundPMF n S) (fun S1 => S1.card < S.card + 1) ≤ (1 / 2 : ℝ) :=
        probR_pushRound_no_growth_le_half hn S h1 hS_lt_half
      have hprob_step : probNatR (binomHalfPMF (R + 1)) (R + 1) (fun x => S.card + x < T) =
          (1 / 2 : ℝ) * A + (1 / 2 : ℝ) * B := by
        have h := probNatBounded_bind_step (P := fun x => S.card + x < T) R
        have h' : probNatR (binomHalfPMF R) R (fun x => S.card + (x + 1) < T) = A := by
          dsimp [A]; congr 1; ext x; congr 1; omega
        rw [h'] at h
        simpa [B] using h
      rw [hprob_step]
      have hcomb : probR (pushRoundPMF n S) (fun S1 => S.card + 1 ≤ S1.card) * A +
          probR (pushRoundPMF n S) (fun S1 => S1.card < S.card + 1) * B ≤
          (1 / 2 : ℝ) * A + (1 / 2 : ℝ) * B := by
        rw [show probR (pushRoundPMF n S) (fun S1 => S.card + 1 ≤ S1.card) =
          1 - probR (pushRoundPMF n S) (fun S1 => S1.card < S.card + 1) by linarith]
        nlinarith
      exact le_trans (Finset.sum_le_sum fun S1 _ => hterm S1) (by rw [hsum_split]; exact hcomb)

/-! ### Stage 1b: Exponential Doubling from `K` to `n / 2` & Complete O(log n) Theorem -/

/-- One round starting from `I = S.card` (with `I < (n + 1) / 2`) achieves at least
    `min (I + I / 4 + 1) ((n + 1) / 2)` infected nodes with probability `≥ 1 - exp(-I / 8)`. -/
theorem probR_pushRound_quarter_growth {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (S : Finset (Fin n)) (hlt : S.card < (n + 1) / 2) :
    probR (pushRoundPMF n S) (fun S' => S'.card < min (S.card + S.card / 4 + 1) ((n + 1) / 2)) ≤
      Real.exp (-((S.card : ℝ) / 8)) := by
  set T := min (S.card + S.card / 4 + 1) ((n + 1) / 2)
  have hT : T ≤ (n + 1) / 2 := min_le_right _ _
  have hdom := probR_kPicks_card_lt_le_binom hn T hT S.card S
  rw [pushRoundPMF]
  have hmono : probNatR (binomHalfPMF S.card) S.card (fun x => S.card + x < T) ≤
      probNatR (binomHalfPMF S.card) S.card (fun x => (x : ℝ) ≤ (S.card : ℝ) / 4) := by
    refine probNatR_mono (binomHalfPMF S.card) S.card (binomHalfPMF_support_le S.card) _ _ fun x hx => ?_
    have hlt_add : S.card + x < S.card + S.card / 4 + 1 := lt_of_lt_of_le hx (min_le_left _ _)
    have hx_le : x ≤ S.card / 4 := by omega
    have hdiv : ((S.card / 4 : ℕ) : ℝ) ≤ (S.card : ℝ) / 4 := by
      have : 4 * (S.card / 4) ≤ S.card := Nat.mul_div_le S.card 4
      have : (4 : ℝ) * ((S.card / 4 : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast this
      linarith
    exact le_trans (Nat.cast_le.mpr hx_le) hdiv
  exact le_trans hdom (le_trans hmono (binomHalf_quarter_tail_le S.card))

/-- Stage 1b: Starting from `K ≤ S.card` (where `exp(-K / 8) ≤ ε`), after `R2` rounds
    if `S'` has not reached `(n + 1) / 2`, then either `R2` rounds multiplied `S.card` by
    `>(5/4)` each time or one round failed `probR_pushRound_quarter_growth`. -/
theorem stage1b_growth_bound {n : ℕ} [NeZero n] (hn : 2 ≤ n) (K : ℕ) (eps : ℝ)
    (heps_nn : 0 ≤ eps)
    (hK : ∀ I : ℕ, K ≤ I → I < (n + 1) / 2 → Real.exp (-((I : ℝ) / 8)) ≤ eps) :
    ∀ (R2 : ℕ) (S : Finset (Fin n)), K ≤ S.card →
      probR (runRounds n R2 S)
        (fun S' => S'.card < (n + 1) / 2 ∧ (S'.card : ℝ) < (5 / 4 : ℝ) ^ R2 * (S.card : ℝ)) ≤
      (R2 : ℝ) * eps
  | 0, S, _ => by
    rw [runRounds, probR, prob_pure]
    simp only [Nat.cast_zero, pow_zero, one_mul, lt_self_iff_false, and_false, ↓reduceIte,
      ENNReal.toReal_zero, zero_mul, le_refl]
  | R2 + 1, S, hKS => by
    set halfN := (n + 1) / 2
    by_cases hreach : halfN ≤ S.card
    · have hz : prob (runRounds n (R2 + 1) S)
          (fun S' => S'.card < halfN ∧ (S'.card : ℝ) < (5 / 4 : ℝ) ^ (R2 + 1) * (S.card : ℝ)) = 0 := by
        rw [prob]
        refine Finset.sum_eq_zero fun S' _ => ?_
        by_cases hsupp : S' ∈ (runRounds n (R2 + 1) S).support
        · have hc : halfN ≤ S'.card := le_trans hreach (Finset.card_le_card (runRounds_support_subset _ hsupp))
          simp [not_lt.mpr hc]
        · rw [PMF.mem_support_iff, not_not] at hsupp
          split_ifs <;> simp [hsupp]
      rw [probR, hz, ENNReal.toReal_zero]
      positivity
    · have hS_lt : S.card < halfN := Nat.lt_of_not_le hreach
      set T := min (S.card + S.card / 4 + 1) halfN
      rw [runRounds, probR, prob_bind]
      have hsum : (∑ S1 : Finset (Fin n), pushRoundPMF n S S1 *
          prob (runRounds n R2 S1)
            (fun S' => S'.card < halfN ∧ (S'.card : ℝ) < (5 / 4 : ℝ) ^ (R2 + 1) * (S.card : ℝ))).toReal =
          ∑ S1 : Finset (Fin n), (pushRoundPMF n S S1).toReal *
            probR (runRounds n R2 S1)
              (fun S' => S'.card < halfN ∧ (S'.card : ℝ) < (5 / 4 : ℝ) ^ (R2 + 1) * (S.card : ℝ)) := by
        rw [ENNReal.toReal_sum (fun S1 _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (prob_ne_top _ _))]
        refine Finset.sum_congr rfl fun S1 _ => ?_
        rw [ENNReal.toReal_mul, probR]
      rw [hsum]
      have hgood : ∀ S1 : Finset (Fin n), S1 ∈ (pushRoundPMF n S).support → T ≤ S1.card →
          probR (runRounds n R2 S1)
            (fun S' => S'.card < halfN ∧ (S'.card : ℝ) < (5 / 4 : ℝ) ^ (R2 + 1) * (S.card : ℝ)) ≤
          (R2 : ℝ) * eps := by
        intro S1 _ hS1_ge_T
        by_cases h1_half : halfN ≤ S1.card
        · have hz : prob (runRounds n R2 S1)
              (fun S' => S'.card < halfN ∧ (S'.card : ℝ) < (5 / 4 : ℝ) ^ (R2 + 1) * (S.card : ℝ)) = 0 := by
            rw [prob]
            refine Finset.sum_eq_zero fun S' _ => ?_
            by_cases hs' : S' ∈ (runRounds n R2 S1).support
            · have hc : halfN ≤ S'.card := le_trans h1_half (Finset.card_le_card (runRounds_support_subset _ hs'))
              simp [not_lt.mpr hc]
            · rw [PMF.mem_support_iff, not_not] at hs'
              split_ifs <;> simp [hs']
          rw [probR, hz, ENNReal.toReal_zero]
          positivity
        · have hS1_ge_q : S.card + S.card / 4 + 1 ≤ S1.card := by omega
          have hS1_mul : (5 / 4 : ℝ) * (S.card : ℝ) ≤ (S1.card : ℝ) := by
            have hrem : S.card ≤ 4 * (S.card / 4) + 3 := by omega
            have h1_r : (S.card : ℝ) + (S.card / 4 : ℕ) + 1 ≤ S1.card := by exact_mod_cast hS1_ge_q
            have hrem_r : (S.card : ℝ) ≤ 4 * ((S.card / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast hrem
            linarith
          have hKS1 : K ≤ S1.card := le_trans hKS (by omega)
          have ih := stage1b_growth_bound hn K eps heps_nn hK R2 S1 hKS1
          refine le_trans (probR_mono _ _ _ (fun S' hS' => ?_)) ih
          refine ⟨hS'.1, ?_⟩
          have hpow_le : (5 / 4 : ℝ) ^ (R2 + 1) * (S.card : ℝ) ≤ (5 / 4 : ℝ) ^ R2 * (S1.card : ℝ) := by
            rw [pow_succ, mul_assoc]
            exact mul_le_mul_of_nonneg_left hS1_mul (by positivity)
          exact lt_of_lt_of_le hS'.2 hpow_le
      have hterm : ∀ S1 : Finset (Fin n),
          (pushRoundPMF n S S1).toReal *
            probR (runRounds n R2 S1)
              (fun S' => S'.card < halfN ∧ (S'.card : ℝ) < (5 / 4 : ℝ) ^ (R2 + 1) * (S.card : ℝ)) ≤
            (if S1.card < T then (pushRoundPMF n S S1).toReal else (pushRoundPMF n S S1).toReal * ((R2 : ℝ) * eps)) := by
        intro S1
        by_cases hsupp : S1 ∈ (pushRoundPMF n S).support
        · by_cases hlt_T : S1.card < T
          · rw [if_pos hlt_T]
            exact mul_le_of_le_one_right ENNReal.toReal_nonneg (probR_le_one _ _)
          · rw [if_neg hlt_T]
            exact mul_le_mul_of_nonneg_left (hgood S1 hsupp (Nat.le_of_not_lt hlt_T)) ENNReal.toReal_nonneg
        · rw [PMF.mem_support_iff, not_not] at hsupp
          simp [hsupp]
      have hsplit : (∑ S1 : Finset (Fin n),
          if S1.card < T then (pushRoundPMF n S S1).toReal else (pushRoundPMF n S S1).toReal * ((R2 : ℝ) * eps)) ≤
          probR (pushRoundPMF n S) (fun S1 => S1.card < T) + (R2 : ℝ) * eps := by
        have h1 : (∑ S1 : Finset (Fin n), if S1.card < T then (pushRoundPMF n S S1).toReal else 0) =
            probR (pushRoundPMF n S) (fun S1 => S1.card < T) := by
          rw [probR, prob, ENNReal.toReal_sum (fun _ _ => by split_ifs <;> simp [PMF.apply_ne_top])]
          refine Finset.sum_congr rfl fun S1 _ => by split_ifs <;> simp
        have h2 : (∑ S1 : Finset (Fin n), if S1.card < T then 0 else (pushRoundPMF n S S1).toReal * ((R2 : ℝ) * eps)) ≤
            (R2 : ℝ) * eps := by
          calc
            (∑ S1 : Finset (Fin n), if S1.card < T then 0 else (pushRoundPMF n S S1).toReal * ((R2 : ℝ) * eps))
                ≤ ∑ S1 : Finset (Fin n), (pushRoundPMF n S S1).toReal * ((R2 : ℝ) * eps) := by
              refine Finset.sum_le_sum fun S1 _ => ?_
              split_ifs
              · positivity
              · exact le_rfl
            _ = (∑ S1 : Finset (Fin n), (pushRoundPMF n S S1).toReal) * ((R2 : ℝ) * eps) := by
              rw [Finset.sum_mul]
            _ = 1 * ((R2 : ℝ) * eps) := by
              congr 1
              rw [← ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _)]
              have hts : (∑ S1 : Finset (Fin n), pushRoundPMF n S S1) = 1 := by
                calc
                  ∑ S1 : Finset (Fin n), pushRoundPMF n S S1
                      = ∑' S1 : Finset (Fin n), pushRoundPMF n S S1 := (tsum_fintype _).symm
                  _ = 1 := (pushRoundPMF n S).tsum_coe
              rw [hts, ENNReal.toReal_one]
            _ = (R2 : ℝ) * eps := one_mul _
        calc
          (∑ S1 : Finset (Fin n),
              if S1.card < T then (pushRoundPMF n S S1).toReal else (pushRoundPMF n S S1).toReal * ((R2 : ℝ) * eps))
              = (∑ S1 : Finset (Fin n), if S1.card < T then (pushRoundPMF n S S1).toReal else 0) +
                (∑ S1 : Finset (Fin n), if S1.card < T then 0 else (pushRoundPMF n S S1).toReal * ((R2 : ℝ) * eps)) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun S1 _ => by split_ifs <;> ring
          _ ≤ probR (pushRoundPMF n S) (fun S1 => S1.card < T) + (R2 : ℝ) * eps := add_le_add h1.le h2
      have hbad : probR (pushRoundPMF n S) (fun S1 => S1.card < T) ≤ eps :=
        le_trans (probR_pushRound_quarter_growth hn S hS_lt) (hK S.card hKS hS_lt)
      have hsum_le : ∑ S1 : Finset (Fin n), (pushRoundPMF n S S1).toReal *
          probR (runRounds n R2 S1)
            (fun S' => S'.card < halfN ∧ (S'.card : ℝ) < (5 / 4 : ℝ) ^ (R2 + 1) * (S.card : ℝ)) ≤
          probR (pushRoundPMF n S) (fun S1 => S1.card < T) + (R2 : ℝ) * eps :=
        le_trans (Finset.sum_le_sum fun S1 _ => hterm S1) hsplit
      have hcast : ((R2 + 1 : ℕ) : ℝ) * eps = eps + (R2 : ℝ) * eps := by push_cast; ring
      rw [hcast]
      linarith

/-- Helper: Composition of `runRounds` across consecutive blocks of rounds. -/
theorem runRounds_add {n : ℕ} [NeZero n] :
    ∀ (R1 R2 : ℕ) (S : Finset (Fin n)),
      runRounds n (R1 + R2) S = (runRounds n R1 S).bind (runRounds n R2)
  | 0, R2, S => by
    rw [zero_add, runRounds, PMF.pure_bind]
  | R1 + 1, R2, S => by
    rw [Nat.add_right_comm, runRounds, runRounds]
    have hfun : runRounds n (R1 + R2) = fun S1 => (runRounds n R1 S1).bind (runRounds n R2) :=
      funext fun S1 => runRounds_add R1 R2 S1
    rw [hfun, ← PMF.bind_bind]

/-- Helper: Splitting failure probability across a sequential pipeline `p.bind f` using
    an intermediate good predicate `G`. -/
theorem probR_bind_split {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → PMF β) (Bad : β → Prop) [DecidablePred Bad]
    (Good : α → Prop) [DecidablePred Good]
    (ε1 ε2 : ℝ) (h1 : probR p (fun a => ¬ Good a) ≤ ε1)
    (h2 : ∀ a, Good a → probR (f a) Bad ≤ ε2)
    (hε2 : 0 ≤ ε2) :
    probR (p.bind f) Bad ≤ ε1 + ε2 := by
  rw [probR, prob_bind]
  have hsum : (∑ a : α, p a * prob (f a) Bad).toReal =
      ∑ a : α, (p a).toReal * probR (f a) Bad := by
    rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (prob_ne_top _ _))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.toReal_mul, probR]
  rw [hsum]
  have hterm : ∀ a : α, (p a).toReal * probR (f a) Bad ≤
      if Good a then (p a).toReal * ε2 else (p a).toReal := by
    intro a
    split_ifs with ha
    · exact mul_le_mul_of_nonneg_left (h2 a ha) ENNReal.toReal_nonneg
    · exact mul_le_of_le_one_right ENNReal.toReal_nonneg (probR_le_one _ _)
  have hsplit : (∑ a : α, if Good a then (p a).toReal * ε2 else (p a).toReal) ≤
      probR p (fun a => ¬ Good a) + ε2 := by
    have ha : (∑ a : α, if Good a then 0 else (p a).toReal) = probR p (fun a => ¬ Good a) := by
      rw [probR, prob, ENNReal.toReal_sum (fun _ _ => by split_ifs <;> simp [PMF.apply_ne_top])]
      refine Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
    have hb : (∑ a : α, if Good a then (p a).toReal * ε2 else 0) ≤ ε2 := by
      calc
        (∑ a : α, if Good a then (p a).toReal * ε2 else 0)
            ≤ ∑ a : α, (p a).toReal * ε2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          split_ifs
          · exact le_rfl
          · positivity
        _ = (∑ a : α, (p a).toReal) * ε2 := by rw [Finset.sum_mul]
        _ = 1 * ε2 := by
          congr 1
          rw [← ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _)]
          have hts : (∑ a : α, p a) = 1 := by
            calc
              ∑ a : α, p a = ∑' a : α, p a := (tsum_fintype _).symm
              _ = 1 := p.tsum_coe
          rw [hts, ENNReal.toReal_one]
        _ = ε2 := one_mul ε2
    calc
      (∑ a : α, if Good a then (p a).toReal * ε2 else (p a).toReal)
          = (∑ a : α, if Good a then (p a).toReal * ε2 else 0) +
            (∑ a : α, if Good a then 0 else (p a).toReal) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => by split_ifs <;> ring
      _ ≤ ε2 + probR p (fun a => ¬ Good a) := add_le_add hb (le_of_eq ha)
      _ = probR p (fun a => ¬ Good a) + ε2 := add_comm _ _
  have h12 : probR p (fun a => ¬ Good a) + ε2 ≤ ε1 + ε2 := by linarith
  exact le_trans (Finset.sum_le_sum fun a _ => hterm a) (le_trans hsplit h12)

/-- **End-to-End O(log n) SWIM Epidemic Dissemination Theorem (Zero Axioms, Zero Sorrys)**:
    Starting from a SINGLE infected node `S₀ = {src}` in a cluster of `n ≥ 2` nodes,
    for any confidence parameter `c ≥ 0`:
    - Stage 1a rounds: `R1 = 4 * Nat.ceil (8 * (c + 5) * Real.log n)` (reaches `min K (n/2)`)
    - Stage 1b rounds: `R2 = 5 * (Nat.ceil (Real.log n) + 1)` (exponential growth to `≥ n/2`)
    - Phase 2 rounds:  `R3 = Nat.ceil (2 * (c + 1) * Real.log n)` (shrinking tail to all `n` nodes)
    Total rounds `R1 + R2 + R3 = O(log n)` infect ALL `n` nodes with probability at least
    `1 - 3 * n ^ (-c)`. -/
theorem full_epidemic_convergence_whp {n : ℕ} [NeZero n] (hn : 2 ≤ n) (c : ℝ) (hc : 0 ≤ c)
    (src : Fin n) :
    let K := Nat.ceil (8 * (c + 5) * Real.log n)
    let R1 := 4 * K
    let R2 := 5 * (Nat.ceil (Real.log n) + 1)
    let R3 := Nat.ceil (2 * (c + 1) * Real.log n)
    probR (runRounds n (R1 + R2 + R3) {src}) (fun S' => S' ≠ Finset.univ) ≤
      3 * (n : ℝ) ^ (-c) := by
  intro K R1 R2 R3
  have hn_pos : (0 : ℝ) < n := by positivity
  have hn_ge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog_pos : 0 < Real.log n := Real.log_pos (by linarith)
  set halfN := (n + 1) / 2
  set T1 := min K halfN
  have hT1_le : T1 ≤ halfN := min_le_right _ _
  -- Stage 1a bound: reaches T1 with failure prob ≤ n ^ (-c)
  have h1a : probR (runRounds n R1 {src}) (fun S1 => ¬ (T1 ≤ S1.card)) ≤ (n : ℝ) ^ (-c) := by
    have hlt_eq : probR (runRounds n R1 {src}) (fun S1 => ¬ (T1 ≤ S1.card)) ≤
        probR (runRounds n R1 {src}) (fun S1 => S1.card < T1) :=
      probR_mono _ _ _ (fun S1 h => Nat.lt_of_not_le h)
    have hdom := probR_runRounds_lt_le_binom hn T1 hT1_le R1 {src} (by simp)
    have hmono : probNatR (binomHalfPMF R1) R1 (fun x => ({src} : Finset (Fin n)).card + x < T1) ≤
        probNatR (binomHalfPMF R1) R1 (fun x => (x : ℝ) ≤ (R1 : ℝ) / 4) := by
      refine probNatR_mono (binomHalfPMF R1) R1 (binomHalfPMF_support_le R1) _ _ fun x hx => ?_
      simp only [Finset.card_singleton] at hx
      have hx_lt_K : x < K := lt_of_lt_of_le (by omega : x < T1) (min_le_left _ _)
      have hx_le_K : (x : ℝ) ≤ K := by exact_mod_cast hx_lt_K.le
      have hR1_div : (K : ℝ) = (R1 : ℝ) / 4 := by
        dsimp [R1]; push_cast; ring
      linarith
    have htail := binomHalf_quarter_tail_le R1
    have hR1_ge : 8 * (c + 5) * Real.log n ≤ (R1 : ℝ) := by
      have hK_ge : 8 * (c + 5) * Real.log n ≤ (K : ℝ) := Nat.le_ceil _
      have : (K : ℝ) ≤ (R1 : ℝ) := by dsimp [R1]; push_cast; linarith [show (0 : ℝ) ≤ K by positivity]
      linarith
    have hexp_bound : Real.exp (-((R1 : ℝ) / 8)) ≤ (n : ℝ) ^ (-c) := by
      have hdiv : -((R1 : ℝ) / 8) ≤ -((c + 5) * Real.log n) := by linarith
      have hexp1 : Real.exp (-((R1 : ℝ) / 8)) ≤ Real.exp (-((c + 5) * Real.log n)) :=
        Real.exp_le_exp.mpr hdiv
      have hexp2 : Real.exp (-((c + 5) * Real.log n)) ≤ Real.exp (-c * Real.log n) := by
        refine Real.exp_le_exp.mpr ?_
        linarith
      rw [Real.rpow_def_of_pos hn_pos]
      have hmul_comm : Real.log n * (-c) = -c * Real.log n := by ring
      rw [hmul_comm]
      exact le_trans hexp1 hexp2
    exact le_trans hlt_eq (le_trans hdom (le_trans hmono (le_trans htail hexp_bound)))
  -- Stage 1b bound: starting from T1 ≤ S1.card, reaches halfN with failure prob ≤ n ^ (-c)
  have h1b : ∀ S1 : Finset (Fin n), T1 ≤ S1.card →
      probR (runRounds n R2 S1) (fun S2 => ¬ (halfN ≤ S2.card)) ≤ (n : ℝ) ^ (-c) := by
    intro S1 hS1
    have hlt_eq : probR (runRounds n R2 S1) (fun S2 => ¬ (halfN ≤ S2.card)) ≤
        probR (runRounds n R2 S1) (fun S2 => S2.card < halfN) :=
      probR_mono _ _ _ (fun S2 h => Nat.lt_of_not_le h)
    refine le_trans hlt_eq ?_
    by_cases halready : halfN ≤ S1.card
    · have hz : prob (runRounds n R2 S1) (fun S2 => S2.card < halfN) = 0 := by
        rw [prob]
        refine Finset.sum_eq_zero fun S2 _ => ?_
        by_cases hsupp : S2 ∈ (runRounds n R2 S1).support
        · have hc : halfN ≤ S2.card := le_trans halready (Finset.card_le_card (runRounds_support_subset _ hsupp))
          simp [not_lt.mpr hc]
        · rw [PMF.mem_support_iff, not_not] at hsupp
          split_ifs <;> simp [hsupp]
      rw [probR, hz, ENNReal.toReal_zero]
      positivity
    · have hS1_lt : S1.card < halfN := Nat.lt_of_not_le halready
      have hKS1 : K ≤ S1.card := by omega
      have h54 : (n : ℝ) ≤ (5 / 4 : ℝ) ^ R2 := by
        have hp5 : Real.exp 1 < (5 / 4 : ℝ) ^ 5 := by
          have := Real.exp_one_lt_d9
          norm_num at *
          linarith
        set m := Nat.ceil (Real.log n) + 1
        have hm : Real.log n ≤ m := by
          have := Nat.le_ceil (Real.log n)
          have : (Nat.ceil (Real.log n) : ℝ) ≤ m := by exact_mod_cast Nat.le_succ _
          linarith
        have hexp_m : (n : ℝ) ≤ Real.exp m := by
          nth_rw 1 [← Real.exp_log hn_pos]
          exact Real.exp_le_exp.mpr hm
        have hpow_m : Real.exp m ≤ ((5 / 4 : ℝ) ^ 5) ^ m := by
          have : Real.exp m = (Real.exp 1) ^ m := by rw [← Real.exp_nat_mul]; simp
          rw [this]
          exact pow_le_pow_left₀ (Real.exp_pos _).le hp5.le m
        have hR2_eq : (5 / 4 : ℝ) ^ R2 = ((5 / 4 : ℝ) ^ 5) ^ m := by
          dsimp [R2]; rw [pow_mul]
        rw [hR2_eq]
        exact le_trans hexp_m hpow_m
      have hmul_S1 : (n : ℝ) ≤ (5 / 4 : ℝ) ^ R2 * (S1.card : ℝ) := by
        have h1_S1 : (1 : ℝ) ≤ S1.card := by
          have : 1 ≤ K := Nat.ceil_pos.mpr (by positivity)
          exact_mod_cast le_trans this hKS1
        nlinarith
      have hmono : probR (runRounds n R2 S1) (fun S2 => S2.card < halfN) ≤
          probR (runRounds n R2 S1) (fun S2 => S2.card < halfN ∧ (S2.card : ℝ) < (5 / 4 : ℝ) ^ R2 * (S1.card : ℝ)) := by
        refine probR_mono _ _ _ fun S2 hS2 => ⟨hS2, ?_⟩
        have hS2_lt_n : (S2.card : ℝ) < n := by
          have h1 : S2.card < halfN := hS2
          have h2 : halfN ≤ n := by dsimp [halfN]; omega
          exact_mod_cast lt_of_lt_of_le h1 h2
        exact lt_of_lt_of_le hS2_lt_n hmul_S1
      set eps := (n : ℝ) ^ (-(c + 5))
      have heps_nn : 0 ≤ eps := by positivity
      have hK_eps : ∀ I : ℕ, K ≤ I → I < halfN → Real.exp (-((I : ℝ) / 8)) ≤ eps := by
        intro I hKI _
        have hK_ge : 8 * (c + 5) * Real.log n ≤ (K : ℝ) := Nat.le_ceil _
        have hI_ge : 8 * (c + 5) * Real.log n ≤ (I : ℝ) := le_trans hK_ge (by exact_mod_cast hKI)
        have hdiv : -((I : ℝ) / 8) ≤ -(c + 5) * Real.log n := by linarith
        rw [show eps = Real.exp (-(c + 5) * Real.log n) by
          dsimp [eps]; rw [Real.rpow_def_of_pos hn_pos]; congr 1; ring]
        exact Real.exp_le_exp.mpr hdiv
      have h1b_raw := stage1b_growth_bound hn K eps heps_nn hK_eps R2 S1 hKS1
      have hR2_le : (R2 : ℝ) ≤ (n : ℝ) ^ (5 : ℕ) := by
        have hlog_le : Real.log n ≤ n := le_trans (Real.log_le_sub_one_of_pos hn_pos) (by linarith)
        have hceil_lt : (Nat.ceil (Real.log n) : ℝ) < Real.log n + 1 := Nat.ceil_lt_add_one hlog_pos.le
        have hR2_bound : (R2 : ℝ) ≤ 5 * (n + 2) := by
          dsimp [R2]; push_cast; linarith
        have hn_pow5 : 5 * (n + 2) ≤ (n : ℝ) ^ (5 : ℕ) := by
          have : (n : ℝ) ^ 2 ≥ 4 := by nlinarith
          have : (n : ℝ) ^ 3 ≥ 8 := by nlinarith
          have : (n : ℝ) ^ 4 ≥ 16 := by nlinarith
          have : (n : ℝ) ^ 5 ≥ 16 * n := by nlinarith
          nlinarith
        exact le_trans hR2_bound hn_pow5
      have heps_mul : (R2 : ℝ) * eps ≤ (n : ℝ) ^ (-c) := by
        have hpow_eq : (n : ℝ) ^ (5 : ℕ) * (n : ℝ) ^ (-(c + 5)) = (n : ℝ) ^ (-c) := by
          rw [← Real.rpow_natCast (n : ℝ) 5, ← Real.rpow_add hn_pos]
          congr 1; ring
        calc
          (R2 : ℝ) * eps ≤ (n : ℝ) ^ (5 : ℕ) * eps := mul_le_mul_of_nonneg_right hR2_le heps_nn
          _ = (n : ℝ) ^ (-c) := hpow_eq
      exact le_trans hmono (le_trans h1b_raw heps_mul)
  -- Phase 2 bound: starting from halfN ≤ S2.card, full dissemination succeeds w.h.p.
  have h2 : ∀ S2 : Finset (Fin n), halfN ≤ S2.card →
      probR (runRounds n R3 S2) (fun S' => S' ≠ Finset.univ) ≤ (n : ℝ) ^ (-c) := by
    intro S2 hS2
    have hP2 : (n : ℝ) / 2 ≤ S2.card := by
      have h2half : n ≤ 2 * halfN := by dsimp [halfN]; omega
      have : (n : ℝ) ≤ 2 * (S2.card : ℝ) := by exact_mod_cast le_trans h2half (Nat.mul_le_mul_left 2 hS2)
      linarith
    exact phase2_convergence_whp hn c R3 (Nat.le_ceil _) S2 hP2
  -- Combine Stage 1a -> Stage 1b -> Phase 2
  rw [runRounds_add (R1 + R2) R3 {src}, runRounds_add R1 R2 {src}]
  have h12 : probR ((runRounds n R1 {src}).bind (runRounds n R2)) (fun S2 => ¬ (halfN ≤ S2.card)) ≤
      (n : ℝ) ^ (-c) + (n : ℝ) ^ (-c) :=
    probR_bind_split (runRounds n R1 {src}) (runRounds n R2) (fun S2 => ¬ (halfN ≤ S2.card))
      (fun S1 => T1 ≤ S1.card) ((n : ℝ) ^ (-c)) ((n : ℝ) ^ (-c)) h1a h1b (by positivity)
  have h12_eq : ((runRounds n R1 {src}).bind (runRounds n R2)).bind (runRounds n R3) =
      (runRounds n (R1 + R2) {src}).bind (runRounds n R3) := by
    rw [runRounds_add R1 R2 {src}]
  have hfull := probR_bind_split ((runRounds n R1 {src}).bind (runRounds n R2)) (runRounds n R3)
    (fun S' => S' ≠ Finset.univ) (fun S2 => halfN ≤ S2.card)
    ((n : ℝ) ^ (-c) + (n : ℝ) ^ (-c)) ((n : ℝ) ^ (-c)) h12 h2 (by positivity)
  linarith

end SwimMathlibProofs

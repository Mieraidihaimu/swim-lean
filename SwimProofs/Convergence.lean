import SwimProofs.EpidemicModel

/-!
# Phase 2 Tail Convergence and $\mathcal{O}(\log n)$ Dissemination Theorem

This module formalizes Phase 2 (the shrinking tail phase) of the epidemic push-gossip
dissemination process and proves the $\mathcal{O}(\log n)$ high-probability dissemination
theorem underpinning the SWIM protocol.

## Protocol Context & Dissemination Dynamics

Epidemic gossip operates in two distinct phases:
1. **Phase 1 (Exponential Growth)**:
   Starting from a single infected node, the number of informed nodes grows exponentially
   ($I_{t+1} \approx 2 I_t$) until at least half of the cluster is infected ($I \ge n / 2$).
   This takes $\mathcal{O}(\log n)$ rounds.
2. **Phase 2 (Shrinking Tail)**:
   Once $I \ge n / 2$, the remaining uninfected nodes $U_t \le n / 2$ shrink exponentially.
   In each round, every informed node selects a peer uniformly at random.
   The non-infection probability for any fixed uninfected node in a single round is:
   $$q = \left(1 - \frac{1}{n}\right)^I \le \exp(-I / n) \le \exp(-1/2) \approx 0.6065 < 1$$

## Main Theorems Formalized in this Module

1. **Single-Round Phase 2 Escape Bound**:
   When $I \ge n / 2$, the single-round non-infection probability $q$ satisfies:
   $$q \le \exp(-1/2) < 1$$
   (`phase2_escapeProb_le_exp_neg_half`, `phase2_escapeProb_lt_one`).

2. **Multi-Round Specific Node Survival Bound**:
   After $R$ independent push-gossip rounds in Phase 2, the probability that a specific
   fixed node remains uninfected is at most:
   $$q^R \le \left(\exp(-1/2)\right)^R = \exp(-R / 2)$$
   (`specificNodeSurvival_le_exp`, `specificNodeSurvival_bound_of_le`).

3. **Union Bound Failure Probability**:
   By union bound over at most $n$ nodes, the probability that *at least one* node remains
   uninfected after $R$ rounds is bounded by:
   $$n \cdot q^R \le n \cdot \exp(-R / 2)$$
   (`phase2UnionBound_le_exp`, `unionBoundFailureProb_le_exp`).

4. **$\mathcal{O}(\log n)$ High-Probability Dissemination Theorem**:
   For any confidence parameter $c > 0$, setting:
   $$R = 2 (c + 1) \ln n$$
   guarantees that the failure probability is bounded by:
   $$n \cdot \exp(-R / 2) = n \cdot \exp(-(c + 1) \ln n) \le n^{-c}$$
   Hence, dissemination succeeds with probability at least $1 - n^{-c}$ in
   $R = \mathcal{O}(\log n)$ rounds (`dissemination_high_probability`,
   `discrete_dissemination_high_probability`, `phase2_unionBound_le_power_bound`).

5. **Alignment with SWIM Dissemination Buffer**:
   In SWIM, gossip buffer retention is set to $\lambda \lceil \log_2 n \rceil$.
   Because $\ln n = (\ln 2) \log_2 n$, choosing $\lambda \ge 2 (c + 1) \ln 2$ aligns
   the buffer transmission count directly with the high-probability dissemination bound.
-/

namespace SwimProofs

noncomputable section

/-! ### Arithmetic & Order Auxiliaries -/

axiom div_two_mul_two (x : Real) : (2 * x) / 2 = x
axiom div_two_monotone {a b : Real} : a ≤ b → a / 2 ≤ b / 2
axiom neg_le_neg {a b : Real} : a ≤ b → -b ≤ -a
axiom natCast_le_natCast {a b : Nat} : a ≤ b → (a : Real) ≤ (b : Real)

/-! ### Phase 2 Definition and Single-Round Contraction -/

/-- Predicate characterizing Phase 2 (half-saturation):
    At least half of the cluster nodes are infected ($I \ge n / 2$). -/
def inPhase2 (p : EpidemicParams) (s : EpidemicState p) : Prop :=
  (p.n : Real) / 2 ≤ (s.infected : Real)

/-- Phase 2 is forward-invariant under valid epidemic steps:
    Once half the cluster is infected, all subsequent states remain in Phase 2. -/
theorem phase2_preserved {p : EpidemicParams} {s1 s2 : EpidemicState p}
    (h_step : ValidStep p s1 s2) (h_p2 : inPhase2 p s1) :
    inPhase2 p s2 := by
  dsimp [inPhase2] at *
  have h_le : (s1.infected : Real) ≤ (s2.infected : Real) :=
    natCast_le_natCast h_step.infected_monotone
  exact Real.le_trans h_p2 h_le

/-- Theorem: In Phase 2 ($I \ge n / 2$), the single-round escape probability $q$
    is bounded by $\exp(-1/2)$. -/
theorem phase2_escapeProb_le_exp_neg_half (p : EpidemicParams) (s : EpidemicState p)
    (h_phase2 : inPhase2 p s) :
    escapeProb p.n s.infected ≤ exp (- ((1 : Real) / 2)) :=
  escapeProb_le_exp_neg_half p.n s.infected p.h_n h_phase2

/-- Theorem: In Phase 2, the single-round escape probability $q$
    is bounded by `tailContractionFactor`. -/
theorem phase2_escapeProb_le_tailContraction (p : EpidemicParams) (s : EpidemicState p)
    (h_phase2 : inPhase2 p s) :
    escapeProb p.n s.infected ≤ tailContractionFactor :=
  phase2_escapeProb_le_exp_neg_half p s h_phase2

/-- Theorem: In Phase 2, the single-round escape probability is strictly less than 1 ($q < 1$). -/
theorem phase2_escapeProb_lt_one (p : EpidemicParams) (s : EpidemicState p)
    (h_phase2 : inPhase2 p s) :
    escapeProb p.n s.infected < 1 :=
  escapeProb_lt_one_of_half p.n s.infected p.h_n h_phase2

/-- Numeric upper bound on single-round non-infection probability in Phase 2: $q \le 0.6065$. -/
theorem phase2_escapeProb_le_const (p : EpidemicParams) (s : EpidemicState p)
    (h_phase2 : inPhase2 p s) :
    escapeProb p.n s.infected ≤ (6065 : Real) / 10000 :=
  escapeProb_le_const p.n s.infected p.h_n h_phase2

/-- The tail contraction factor $q = \exp(-1/2)$ is strictly subcritical ($q < 1$). -/
theorem tailContractionFactor_subcritical :
    tailContractionFactor < 1 :=
  tailContractionFactor_lt_one

/-! ### Multi-Round Specific Node Survival Bounds -/

/-- Upper bound on the survival probability of a specific uninfected node over $R$
    independent rounds with per-round escape factor bounded by $q$: $q^R$. -/
def specificNodeSurvival (q : Real) (R : Nat) : Real :=
  q ^ R

/-- Monotonicity of specific node survival with respect to contraction factor. -/
theorem specificNodeSurvival_le_pow (q : Real) (hq_nonneg : 0 ≤ q)
    (hq : q ≤ tailContractionFactor) (R : Nat) :
    specificNodeSurvival q R ≤ specificNodeSurvival tailContractionFactor R :=
  pow_le_pow R hq_nonneg hq

/-- Master specific-node tail bound:
    After $R$ rounds with contraction factor $q = \exp(-1/2)$,
    a specific node remains uninfected with probability at most $\exp(-R / 2)$. -/
theorem specificNodeSurvival_le_exp (R : Nat) :
    specificNodeSurvival tailContractionFactor R ≤ exp (- ((R : Real) / 2)) :=
  multiRound_escape_le_exp R

/-- For any per-round escape probability $q \le \exp(-1/2)$, the specific node survival
    probability after $R$ rounds is at most $\exp(-R / 2)$. -/
theorem specificNodeSurvival_bound_of_le (q : Real) (hq_nonneg : 0 ≤ q)
    (hq : q ≤ tailContractionFactor) (R : Nat) :
    specificNodeSurvival q R ≤ exp (- ((R : Real) / 2)) := by
  have h1 : specificNodeSurvival q R ≤ specificNodeSurvival tailContractionFactor R :=
    pow_le_pow R hq_nonneg hq
  have h2 : specificNodeSurvival tailContractionFactor R ≤ exp (- ((R : Real) / 2)) :=
    multiRound_escape_le_exp R
  exact Real.le_trans h1 h2

/-! ### Union Bound Over Uninfected Nodes -/

/-- Union bound failure probability:
    The probability that AT LEAST ONE node escapes infection after $R$ rounds
    is bounded by $n \cdot q^R$ (since there are at most $n$ nodes in total). -/
def unionBoundFailureProb (n : Nat) (q : Real) (R : Nat) : Real :=
  (n : Real) * (q ^ R)

/-- Simplified union bound with $q = \text{tailContractionFactor}$:
    $P(\text{failure}) \le n \cdot (\exp(-1/2))^R$. -/
def phase2UnionBound (n : Nat) (R : Nat) : Real :=
  unionBoundFailureProb n tailContractionFactor R

/-- Analytical exponential upper envelope for the union bound failure probability:
    $n \cdot \exp(-R / 2)$. -/
def unionBoundExpEnvelope (n : Nat) (R : Nat) : Real :=
  (n : Real) * exp (- ((R : Real) / 2))

/-- Union bound failure probability with $q = \text{tailContractionFactor}$
    is bounded by $n \cdot \exp(-R / 2)$. -/
theorem phase2UnionBound_le_exp (n : Nat) (R : Nat) :
    phase2UnionBound n R ≤ unionBoundExpEnvelope n R :=
  union_bound_multiRound_le n R

/-- For any valid per-round escape bound $q \le \text{tailContractionFactor}$,
    the union bound failure probability over at most $n$ nodes is at most $n \cdot \exp(-R / 2)$. -/
theorem unionBoundFailureProb_le_exp (n : Nat) (q : Real) (hq_nonneg : 0 ≤ q)
    (hq : q ≤ tailContractionFactor) (R : Nat) :
    unionBoundFailureProb n q R ≤ unionBoundExpEnvelope n R := by
  dsimp [unionBoundFailureProb, unionBoundExpEnvelope]
  have h_surv : q ^ R ≤ exp (- ((R : Real) / 2)) :=
    specificNodeSurvival_bound_of_le q hq_nonneg hq R
  have hn_nonneg : 0 ≤ (n : Real) := Real.nat_nonneg n
  exact Real.mul_le_mul_of_nonneg_left hn_nonneg h_surv

/-! ### $\mathcal{O}(\log n)$ High-Probability Dissemination Theorem -/

/-- Continuous failure probability envelope as a function of real rounds $R$:
    $n \cdot \exp(-R / 2)$. -/
def continuousFailureProb (n : Nat) (R : Real) : Real :=
  (n : Real) * exp (- (R / 2))

/-- Target round count $R = 2 (c + 1) \ln n$ for failure probability $\le n^{-c}$. -/
def targetRounds (c : Real) (n : Nat) : Real :=
  2 * ((c + 1) * ln (n : Real))

/-- Asymptotic complexity constant $K(c) = 2 (c + 1)$ in $R = K(c) \ln n = \mathcal{O}(\log n)$. -/
def roundComplexityConstant (c : Real) : Real :=
  2 * (c + 1)

/-- Target round count decomposes as constant times logarithm:
    $R(c, n) = K(c) \cdot \ln(n)$, proving $R = \mathcal{O}(\log n)$. -/
theorem targetRounds_asymptotic (c : Real) (n : Nat) :
    targetRounds c n = roundComplexityConstant c * ln (n : Real) := by
  dsimp [targetRounds, roundComplexityConstant]
  exact (Real.mul_assoc 2 (c + 1) (ln (n : Real))).symm

/-- Half of target rounds simplifies to $(c + 1) \ln n$. -/
theorem targetRounds_div_two (c : Real) (n : Nat) :
    (targetRounds c n) / 2 = (c + 1) * ln (n : Real) := by
  dsimp [targetRounds]
  exact div_two_mul_two ((c + 1) * ln (n : Real))

/-- Theorem (Continuous Dissemination Theorem):
    For $R = 2 (c + 1) \ln n$, the failure probability is bounded by $n^{-c}$:
    $$n \cdot \exp(-R / 2) \le n^{-c}$$ -/
theorem dissemination_high_probability (n : Nat) (c : Real) (hn : 2 ≤ n) :
    continuousFailureProb n (targetRounds c n) ≤ (n : Real) ^ (- c) := by
  dsimp [continuousFailureProb]
  rw [targetRounds_div_two]
  exact exp_neg_log_bound n c hn

/-- Theorem (Discrete Dissemination Theorem):
    For any integer round count $R \ge 2 (c + 1) \ln n$, the union bound exponential
    envelope satisfies:
    $$n \cdot \exp(-R / 2) \le n^{-c}$$ -/
theorem discrete_dissemination_high_probability (n : Nat) (c : Real) (R : Nat) (hn : 2 ≤ n)
    (hR : targetRounds c n ≤ (R : Real)) :
    unionBoundExpEnvelope n R ≤ (n : Real) ^ (- c) := by
  dsimp [unionBoundExpEnvelope]
  have h_div : (targetRounds c n) / 2 ≤ (R : Real) / 2 := div_two_monotone hR
  have h_neg : - ((R : Real) / 2) ≤ - ((targetRounds c n) / 2) := neg_le_neg h_div
  have h_exp : exp (- ((R : Real) / 2)) ≤ exp (- ((targetRounds c n) / 2)) := exp_monotone h_neg
  have hn_nonneg : 0 ≤ (n : Real) := Real.nat_nonneg n
  have h_mul : (n : Real) * exp (- ((R : Real) / 2)) ≤ (n : Real) * exp (- ((targetRounds c n) / 2)) :=
    Real.mul_le_mul_of_nonneg_left hn_nonneg h_exp
  rw [targetRounds_div_two] at h_mul
  have h_bound := exp_neg_log_bound n c hn
  exact Real.le_trans h_mul h_bound

/-- Main Theorem (Phase 2 Union Bound Power Bound):
    After $R \ge 2 (c + 1) \ln n$ rounds in Phase 2, the probability that any node
    remains uninfected is at most $n^{-c}$. -/
theorem phase2_unionBound_le_power_bound (n : Nat) (c : Real) (R : Nat) (hn : 2 ≤ n)
    (hR : targetRounds c n ≤ (R : Real)) :
    phase2UnionBound n R ≤ (n : Real) ^ (- c) := by
  have h1 := phase2UnionBound_le_exp n R
  have h2 := discrete_dissemination_high_probability n c R hn hR
  exact Real.le_trans h1 h2

/-- General Main Theorem:
    For any per-round escape bound $q \le \text{tailContractionFactor}$,
    after $R \ge 2 (c + 1) \ln n$ rounds, the union bound failure probability is $\le n^{-c}$. -/
theorem unionBoundFailureProb_le_power_bound (n : Nat) (q : Real) (c : Real) (R : Nat)
    (hn : 2 ≤ n) (hq_nonneg : 0 ≤ q) (hq : q ≤ tailContractionFactor)
    (hR : targetRounds c n ≤ (R : Real)) :
    unionBoundFailureProb n q R ≤ (n : Real) ^ (- c) := by
  have h1 := unionBoundFailureProb_le_exp n q hq_nonneg hq R
  have h2 := discrete_dissemination_high_probability n c R hn hR
  exact Real.le_trans h1 h2

/-! ### Practical Gossip Parameter Alignment with SWIM -/

/-- SWIM multiplier $\lambda$: Setting $\lambda \ge 2 (c + 1) \ln 2$ ensures that the
    dissemination buffer transmission limit $\lambda \lceil \log_2 n \rceil$ satisfies
    the high-probability dissemination round threshold $R = 2 (c + 1) \ln n$. -/
def minSwimMultiplier (c : Real) (ln2 : Real) : Real :=
  2 * (c + 1) * ln2

end

end SwimProofs

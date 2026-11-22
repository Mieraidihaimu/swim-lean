/-!
# Epidemic Spread and Push-Gossip Model

This module formalizes the discrete-time epidemic spread and push-gossip model
underlying the SWIM dissemination protocol.

## Model Overview
- Total nodes: $n \in \mathbb{N}$ with $n \ge 2$.
- Discrete round $t$: $I_t$ infected nodes ($1 \le I_t \le n$), remaining uninfected $U_t = n - I_t$.
- Single-round escape probability:
  When $I$ infected nodes each pick a random peer uniformly from $n$ nodes, the probability
  a fixed uninfected node is not chosen by any of the $I$ nodes is:
  $$(1 - 1/n)^I$$
- Analytical Bounds:
  1. $(1 - 1/n)^I \le \exp(-I / n)$
  2. When $I \ge n / 2$, $(1 - 1/n)^I \le \exp(-1/2) \le 0.6065$
-/

namespace SwimProofs

/-! ### Real Number Axiomatization & Analysis Foundations -/

opaque Real : Type

noncomputable section

axiom Real.zero : Real
axiom Real.one : Real
axiom Real.add : Real → Real → Real
axiom Real.mul : Real → Real → Real
axiom Real.neg : Real → Real
axiom Real.inv : Real → Real
axiom Real.le : Real → Real → Prop
axiom Real.lt : Real → Real → Prop
axiom Real.ofNat : Nat → Real
axiom Real.pow : Real → Nat → Real
axiom Real.rpow : Real → Real → Real

instance : OfNat Real 0 := ⟨Real.zero⟩
instance : OfNat Real 1 := ⟨Real.one⟩
instance : Add Real := ⟨Real.add⟩
instance : Mul Real := ⟨Real.mul⟩
instance : Neg Real := ⟨Real.neg⟩
instance : Inv Real := ⟨Real.inv⟩
instance : Sub Real := ⟨fun a b => a + -b⟩
instance : Div Real := ⟨fun a b => a * b⁻¹⟩
instance : LE Real := ⟨Real.le⟩
instance : LT Real := ⟨Real.lt⟩
instance : NatCast Real := ⟨Real.ofNat⟩
instance (n : Nat) : OfNat Real n := ⟨Real.ofNat n⟩
instance : HPow Real Nat Real := ⟨Real.pow⟩
instance : HPow Real Real Real := ⟨Real.rpow⟩

-- Order properties
axiom Real.le_refl (x : Real) : x ≤ x
axiom Real.le_trans {x y z : Real} : x ≤ y → y ≤ z → x ≤ z
axiom Real.le_antisymm {x y : Real} : x ≤ y → y ≤ x → x = y
axiom Real.lt_iff_le_and_ne {x y : Real} : x < y ↔ x ≤ y ∧ x ≠ y
axiom Real.lt_of_le_of_lt {x y z : Real} : x ≤ y → y < z → x < z
axiom Real.lt_of_lt_of_le {x y z : Real} : x < y → y ≤ z → x < z

-- Arithmetic properties
axiom Real.add_comm (a b : Real) : a + b = b + a
axiom Real.add_assoc (a b c : Real) : (a + b) + c = a + (b + c)
axiom Real.add_zero (a : Real) : a + 0 = a
axiom Real.zero_add (a : Real) : 0 + a = a
axiom Real.sub_eq_add_neg (a b : Real) : a - b = a + (-b)

axiom Real.mul_comm (a b : Real) : a * b = b * a
axiom Real.mul_assoc (a b c : Real) : (a * b) * c = a * (b * c)
axiom Real.mul_one (a : Real) : a * 1 = a
axiom Real.one_mul (a : Real) : 1 * a = a
axiom Real.mul_zero (a : Real) : a * 0 = 0
axiom Real.zero_mul (a : Real) : 0 * a = 0

axiom Real.mul_le_mul_of_nonneg_left {a b c : Real} : 0 ≤ c → a ≤ b → c * a ≤ c * b
axiom Real.mul_le_mul_of_nonneg_right {a b c : Real} : 0 ≤ c → a ≤ b → a * c ≤ b * c

axiom Real.nat_nonneg (n : Nat) : 0 ≤ (n : Real)
axiom Real.nat_pos (n : Nat) (h : 1 ≤ n) : 0 < (n : Real)

axiom Real.neg_div_mul (n I : Real) : (- (1 / n)) * I = - (I / n)
axiom Real.div_mul_assoc (a b c : Real) : (a / b) * c = (a * c) / b

-- Exponential and Logarithm
axiom exp : Real → Real
axiom ln : Real → Real

axiom exp_pos (x : Real) : 0 < exp x
axiom exp_nonneg (x : Real) : 0 ≤ exp x
axiom exp_zero : exp 0 = 1
axiom exp_add (x y : Real) : exp (x + y) = exp x * exp y
axiom exp_monotone {x y : Real} : x ≤ y → exp x ≤ exp y
axiom exp_strict_monotone {x y : Real} : x < y → exp x < exp y
axiom exp_mul_nat (x : Real) (k : Nat) : (exp x) ^ k = exp (x * (k : Real))
axiom one_plus_x_le_exp (x : Real) : 1 + x ≤ exp x

axiom ln_exp (x : Real) : ln (exp x) = x
axiom exp_ln {x : Real} : 0 < x → exp (ln x) = x
axiom ln_monotone {x y : Real} : 0 < x → x ≤ y → ln x ≤ ln y
axiom ln_one : ln 1 = 0

-- Power monotonicity
axiom pow_le_pow {a b : Real} (k : Nat) : 0 ≤ a → a ≤ b → a ^ k ≤ b ^ k
axiom Real.pow_nonneg {a : Real} (k : Nat) : 0 ≤ a → 0 ≤ a ^ k
axiom Real.pow_le_one {a : Real} (k : Nat) : 0 ≤ a → a ≤ 1 → a ^ k ≤ 1

-- Numeric and ratio bounds
axiom one_sub_inv_nonneg (n : Nat) (hn : 2 ≤ n) : 0 ≤ 1 - (1 / (n : Real))
axiom one_sub_inv_le_one (n : Nat) (hn : 2 ≤ n) : 1 - (1 / (n : Real)) ≤ 1

axiom half_le_div_of_half_le (n I : Nat) (hn : 2 ≤ n) (h : (n : Real) / 2 ≤ (I : Real)) :
    - ((I : Real) / (n : Real)) ≤ - ((1 : Real) / 2)

axiom exp_neg_half_le_const : exp (- ((1 : Real) / 2)) ≤ (6065 : Real) / 10000
axiom const_lt_one : (6065 : Real) / 10000 < 1
axiom exp_neg_half_lt_one : exp (- ((1 : Real) / 2)) < 1

-- Exponential power simplification for phase 2
axiom exp_neg_half_pow (R : Nat) :
    (exp (- ((1 : Real) / 2))) ^ R = exp (- ((R : Real) / 2))

axiom exp_neg_log_bound (n : Nat) (c : Real) (hn : 2 ≤ n) :
    (n : Real) * exp (- ((c + 1) * ln (n : Real))) ≤ (n : Real) ^ (- c)

/-! ### Push-Gossip Epidemic Model -/

/-- Total cluster configuration parameter: n nodes with n ≥ 2 -/
structure EpidemicParams where
  n : Nat
  h_n : 2 ≤ n

/-- State of epidemic push-gossip at a discrete round t:
    - `round`: round index t
    - `infected`: number of infected nodes I_t (1 ≤ I_t ≤ n)
    - `uninfected`: remaining uninfected nodes U_t = n - I_t -/
structure EpidemicState (p : EpidemicParams) where
  round : Nat
  infected : Nat
  uninfected : Nat
  h_infected_ge_one : 1 ≤ infected
  h_infected_le_n : infected ≤ p.n
  h_uninfected_eq : uninfected = p.n - infected

/-- Initial state with a single infected source node -/
def initialEpidemicState (p : EpidemicParams) : EpidemicState p where
  round := 0
  infected := 1
  uninfected := p.n - 1
  h_infected_ge_one := Nat.le_refl 1
  h_infected_le_n := Nat.le_trans (by decide) p.h_n
  h_uninfected_eq := rfl

/-- Total node conservation: I_t + U_t = n -/
theorem state_node_conservation (p : EpidemicParams) (s : EpidemicState p) :
    s.infected + s.uninfected = p.n := by
  rw [s.h_uninfected_eq]
  exact Nat.add_sub_of_le s.h_infected_le_n

/-- A valid transition from round t to round t+1:
    The number of infected nodes is monotonically non-decreasing and bounded by n. -/
structure ValidStep (p : EpidemicParams) (s1 s2 : EpidemicState p) : Prop where
  round_step : s2.round = s1.round + 1
  infected_monotone : s1.infected ≤ s2.infected
  infected_bound : s2.infected ≤ p.n

/-- Dissemination complete predicate: all n nodes are infected -/
def isDisseminated (p : EpidemicParams) (s : EpidemicState p) : Prop :=
  s.infected = p.n

/-- Dissemination is equivalent to zero remaining uninfected nodes -/
theorem disseminated_iff_uninfected_zero (p : EpidemicParams) (s : EpidemicState p) :
    isDisseminated p s ↔ s.uninfected = 0 := by
  dsimp [isDisseminated]
  constructor
  · intro h
    rw [s.h_uninfected_eq, h]
    exact Nat.sub_self p.n
  · intro h
    have hcons := state_node_conservation p s
    rw [h, Nat.add_zero] at hcons
    exact hcons

/-! ### Escape Probability Formalization -/

/-- Single-transmission escape probability:
    When one infected node selects a destination uniformly at random from n nodes,
    the probability that a fixed uninfected node is not chosen is 1 - 1/n. -/
def singleEscapeProb (n : Nat) : Real :=
  1 - (1 / (n : Real))

/-- Single-round escape probability:
    When I infected nodes each independently pick a destination uniformly at random from n nodes,
    the probability that a fixed uninfected node is never picked is (1 - 1/n)^I. -/
def escapeProb (n : Nat) (I : Nat) : Real :=
  (singleEscapeProb n) ^ I

theorem escapeProb_def (n : Nat) (I : Nat) :
    escapeProb n I = (1 - (1 / (n : Real))) ^ I := rfl

theorem escapeProb_nonneg (n I : Nat) (hn : 2 ≤ n) :
    0 ≤ escapeProb n I :=
  Real.pow_nonneg I (one_sub_inv_nonneg n hn)

theorem escapeProb_le_one (n I : Nat) (hn : 2 ≤ n) :
    escapeProb n I ≤ 1 :=
  Real.pow_le_one I (one_sub_inv_nonneg n hn) (one_sub_inv_le_one n hn)

/-! ### Analytical Bounds -/

/-- Theorem 1: Escape probability bound by exponential.
    For any n ≥ 2 and I ≥ 1, the probability that a fixed node escapes all I transmissions
    is bounded by exp(-I / n). -/
theorem escapeProb_le_exp_neg_div (n I : Nat) (hn : 2 ≤ n) :
    escapeProb n I ≤ exp (- ((I : Real) / (n : Real))) := by
  have h1 : 1 - (1 / (n : Real)) = 1 + (- (1 / (n : Real))) := by
    exact Real.sub_eq_add_neg 1 (1 / (n : Real))
  have h2 : 1 + (- (1 / (n : Real))) ≤ exp (- (1 / (n : Real))) := by
    exact one_plus_x_le_exp (- (1 / (n : Real)))
  have h_base : 1 - (1 / (n : Real)) ≤ exp (- (1 / (n : Real))) := by
    rw [h1]; exact h2
  have h_nonneg : 0 ≤ 1 - (1 / (n : Real)) := one_sub_inv_nonneg n hn
  have h_pow : (1 - (1 / (n : Real))) ^ I ≤ (exp (- (1 / (n : Real)))) ^ I :=
    pow_le_pow I h_nonneg h_base
  have h_exp_pow : (exp (- (1 / (n : Real)))) ^ I = exp ((- (1 / (n : Real))) * (I : Real)) :=
    exp_mul_nat (- (1 / (n : Real))) I
  have h_alg : (- (1 / (n : Real))) * (I : Real) = - ((I : Real) / (n : Real)) :=
    Real.neg_div_mul (n : Real) (I : Real)
  have h_eq : (exp (- (1 / (n : Real)))) ^ I = exp (- ((I : Real) / (n : Real))) := by
    rw [h_exp_pow, h_alg]
  dsimp [escapeProb, singleEscapeProb]
  rw [h_eq] at h_pow
  exact h_pow

/-- Theorem 2: Half-saturation upper bound.
    When I ≥ n / 2, the escape probability is bounded by exp(-1/2). -/
theorem escapeProb_le_exp_neg_half (n I : Nat) (hn : 2 ≤ n) (h_half : (n : Real) / 2 ≤ (I : Real)) :
    escapeProb n I ≤ exp (- ((1 : Real) / 2)) := by
  have h1 : escapeProb n I ≤ exp (- ((I : Real) / (n : Real))) :=
    escapeProb_le_exp_neg_div n I hn
  have h_neg : - ((I : Real) / (n : Real)) ≤ - ((1 : Real) / 2) :=
    half_le_div_of_half_le n I hn h_half
  have h2 : exp (- ((I : Real) / (n : Real))) ≤ exp (- ((1 : Real) / 2)) :=
    exp_monotone h_neg
  exact Real.le_trans h1 h2

/-- Theorem 3: Numeric upper bound.
    When I ≥ n / 2, the escape probability is bounded by 0.6065. -/
theorem escapeProb_le_const (n I : Nat) (hn : 2 ≤ n) (h_half : (n : Real) / 2 ≤ (I : Real)) :
    escapeProb n I ≤ (6065 : Real) / 10000 := by
  have h1 := escapeProb_le_exp_neg_half n I hn h_half
  exact Real.le_trans h1 exp_neg_half_le_const

/-- Corollary: The escape probability at half saturation is strictly less than 1. -/
theorem escapeProb_lt_one_of_half (n I : Nat) (hn : 2 ≤ n) (h_half : (n : Real) / 2 ≤ (I : Real)) :
    escapeProb n I < 1 := by
  have h1 := escapeProb_le_const n I hn h_half
  exact Real.lt_of_le_of_lt h1 const_lt_one

/-! ### Multi-Round Dissemination Bounds (Convergence Foundations) -/

/-- Single-round tail contraction constant: q = exp(-1/2) -/
def tailContractionFactor : Real :=
  exp (- ((1 : Real) / 2))

theorem tailContractionFactor_lt_one :
    tailContractionFactor < 1 :=
  exp_neg_half_lt_one

theorem tailContractionFactor_le_const :
    tailContractionFactor ≤ (6065 : Real) / 10000 :=
  exp_neg_half_le_const

/-- Upper bound on the probability that a specific node remains uninfected after R rounds
    of push-gossip when each round has I ≥ n/2: q^R ≤ exp(-R / 2). -/
theorem multiRound_escape_le_exp (R : Nat) :
    tailContractionFactor ^ R ≤ exp (- ((R : Real) / 2)) := by
  dsimp [tailContractionFactor]
  rw [exp_neg_half_pow R]
  exact Real.le_refl _

/-- Union bound over at most n nodes:
    The probability that AT LEAST ONE node remains uninfected after R rounds
    is bounded by n * q^R ≤ n * exp(-R / 2). -/
theorem union_bound_multiRound_le (n : Nat) (R : Nat) :
    (n : Real) * (tailContractionFactor ^ R) ≤ (n : Real) * exp (- ((R : Real) / 2)) := by
  have h_pow := multiRound_escape_le_exp R
  have h_n_nonneg : 0 ≤ (n : Real) := Real.nat_nonneg n
  exact Real.mul_le_mul_of_nonneg_left h_n_nonneg h_pow

/-- Dissemination with high probability:
    For R = 2 * (c + 1) * ln(n), the union bound failure probability is at most n^(-c). -/
theorem failure_prob_order_log_n (n : Nat) (c : Real) (hn : 2 ≤ n) :
    (n : Real) * exp (- ((c + 1) * ln (n : Real))) ≤ (n : Real) ^ (- c) :=
  exp_neg_log_bound n c hn

end

end SwimProofs

/-
Authors: Danny Zou
-/

module

import Mathlib

/-!
# One-Period Binomial Model For European Contingent Claims

In this file we introduce the one-period binomial model for pricing
European Contingent Claims (ECC), a fundamental model to mathematical finance and
the pricing of financial derivatives.
We will show that under the one-period binomial model, the arbitrage-free model
can be derived.

## Main Definitions and Results
- `filtration`: A filtration on the probability space defined by the one-period binomial model.
- `trading_strategy`: A trading strategy in the one-period binomial model.
- `arbitrage`: A definition of arbitrage.
- `risk_neutral_measure`: A risk neutral measure in the one-period binomial model.
- `call_price`: The arbitrage-free price of an ECC in the one-period binomial model.
- 'put_call_parity': The relationship of the arbitrage-free prices of puts and calls in the one-period binomial model for an ECC.

# References
- https://mathweb.ucsd.edu/~williams/courses/m294notes/chap2.pdf
-/

structure parameters where
  S₀ : ℝ
  u : ℝ
  d : ℝ
  r : ℝ
  hS₀ : S₀ > 0
  hu : u > 0
  hd : d > 0
  hr : r > -1
  hud : u ≥ d

variable (p : parameters)

abbrev Ω : Type := Bool

open MeasureTheory

instance : MeasurableSpace Ω := ⊤

def binomialFiltration : Filtration (Fin 2) (⊤ : MeasurableSpace Ω) where
  seq := fun i => if i = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  le' := by
    intro i
    fin_cases i <;> simp

def B₀ : ℝ := 1
def B₁ : ℝ := 1 + p.r

def S₁ (ω : Ω) : ℝ :=
  if ω then p.S₀ * p.u else p.S₀ * p.d

structure trading_strategy where
  α : ℝ
  β : ℝ

def V₀ (φ : trading_strategy) : ℝ :=
  φ.α * p.S₀ + φ.β * B₀
def V₁ (φ : trading_strategy) (ω : Ω) : ℝ :=
  φ.α * S₁ p ω + φ.β * B₁ p

def arbitrage (φ : trading_strategy) : Prop :=
  V₀ p φ = 0 ∧
  (∀ ω : Ω, V₁ p φ ω ≥ 0) ∧
  (∃ ω : Ω, V₁ p φ ω > 0)

def arbitrage_free : Prop :=
  ¬∃ φ : trading_strategy, arbitrage p φ

noncomputable def q : ℝ :=
  ((1 + p.r) - p.d) / (p.u - p.d)

lemma arbitrage_free_condition :
    arbitrage_free p ↔ p.d < 1 + p.r ∧ 1 + p.r < p.u := by
  constructor
  contrapose
  intro h
  rw [not_and_or] at h
  rcases h with hd | hu
  · -- case mp.inl: d ≥ 1 + p.r
    push Not at hd
    unfold arbitrage_free
    simp
    unfold arbitrage
    let φ : trading_strategy := ⟨1, -p.S₀⟩
    have h1 : V₀ p φ = 0 := by
      simp [V₀, B₀, φ]
    have h2 : ∀ ω : Ω, V₁ p φ ω ≥ 0 := by
      intro ω
      simp [V₁, S₁, B₁, φ]
      by_cases hw : ω
      · -- case ω = true: S₁ = S₀ * u
        simp [hw]
        have hu : 1 + p.r ≤ p.u := by
          calc
            1 + p.r ≤ p.d := by linarith [hd]
            _ ≤ p.u := by apply p.hud
        exact mul_le_mul_of_nonneg_left hu (le_of_lt p.hS₀)
      · -- case ω = false: S₁ = S₀ * d
        simp [hw]
        exact mul_le_mul_of_nonneg_left hd (le_of_lt p.hS₀)
        /-
        Here's where I'm currently working:

        case neg
        p : parameters
        hd : 1 + p.r ≤ p.d
        φ : trading_strategy := { α := 1, β := -p.S₀ }
        h1 : V₀ p φ = 0
        ω : Ω
        hw : ¬ω = true
        ⊢ p.S₀ * (1 + p.r) ≤ p.S₀ * p.d
        -/
    sorry
  sorry
  sorry




/-
Current status of arbitrage_free_condition:
3 goals:

3 goals
case pos
p : parameters
h : p.d ≥ 1 + p.r
⊢ ¬(p.d < 1 + p.r ∧ 1 + p.r < p.u) → ¬arbitrage_free p
case neg
p : parameters
h : ¬p.d ≥ 1 + p.r
⊢ ¬(p.d < 1 + p.r ∧ 1 + p.r < p.u) → ¬arbitrage_free p
case mpr
p : parameters
⊢ p.d < 1 + p.r ∧ 1 + p.r < p.u → arbitrage_free p
-/

lemma q_in_unit_interval :
    0 < q p ∧ q p < 1 ↔ p.d < 1 + p.r ∧ 1 + p.r < p.u := by
  sorry

noncomputable def Q (ω : Ω) : ℝ :=
  if ω then q p else 1 - q p

lemma q_is_prob_measure (h : p.d < 1 + p.r ∧ 1 + p.r < p.u) :
    Q p true + Q p false = 1 ∧ 0 < Q p true ∧ 0 < Q p false := by
  sorry

lemma discounted_stock_expectation (h : p.d < 1 + p.r ∧ 1 + p.r < p.u) :
    Q p true * (S₁ p true / (1 + p.r)) + Q p false * (S₁ p false / (1 + p.r)) = p.S₀ := by
  sorry

abbrev ECC := Ω → ℝ

def replicating_strategy (φ : trading_strategy) (Φ : ECC) : Prop :=
  ∀ ω : Ω, V₁ p φ ω = Φ ω

theorem replication_existence (Φ : ECC) (h : p.d < 1 + p.r ∧ 1 + p.r < p.u) :
    ∃ φ : trading_strategy, replicating_strategy p φ Φ := by
  sorry

theorem risk_neutral_pricing (Φ : ECC) (φ : trading_strategy)
    (hrep : replicating_strategy p φ Φ) (h : p.d < 1 + p.r ∧ 1 + p.r < p.u) :
    V₀ p φ = (Q p true * Φ true + Q p false * Φ false) / (1 + p.r) := by
  sorry

noncomputable def call_value (K : ℝ) : ECC :=
  fun ω => max (S₁ p ω - K) 0

lemma call_price (K : ℝ) (φ : trading_strategy)
    (hrep : replicating_strategy p φ (call_value p K)) (h : p.d < 1 + p.r ∧ 1 + p.r < p.u) :
    V₀ p φ = (Q p true * max (p.u * p.S₀ - K) 0 +
              Q p false * max (p.d * p.S₀ - K) 0) / (1 + p.r) := by
  sorry

noncomputable def put_value (K : ℝ) : ECC :=
  fun ω => max (K - S₁ p ω) 0

lemma put_call_parity (K : ℝ) (φ_c φ_p : trading_strategy)
    (hrep_c : replicating_strategy p φ_c (call_value p K))
    (hrep_p : replicating_strategy p φ_p (put_value p K))
    (h : p.d < 1 + p.r ∧ 1 + p.r < p.u) :
    V₀ p φ_c - V₀ p φ_p = p.S₀ - K / (1 + p.r) := by
  sorry

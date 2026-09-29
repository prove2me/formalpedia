-- Prove2me | solution 1 for GodelCasinoAsymmetricOdds.edge_iff_outside_no_bet_interval
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:45:18.208427+00:00
-- url     : https://prove2.me/submissions/7e02f592-b588-4f70-8fe6-835a2488ae70

-- Sol generated from Logic/GodelCasinoAsymmetricOdds.lean
import Mathlib
import Definitions.Def_Logic_GodelCasinoAsymmetricOdds
import Theorems.Thm_GodelCasinoAsymmetricOdds_expOdds_eq
/-
# Gödel's Casino: asymmetric odds, transaction costs, and abstention

This file advances the randomized casino model from symmetric ±1 payoffs to
asymmetric odds.  A correct bet earns `a`, while an incorrect bet loses `b`.
The resulting break-even probability is `b / (a+b)` for betting true and
`a / (a+b)` for betting false.  We also add a zero-payoff abstention option.
-/

open GodelCasinoAsymmetricOdds

open Finset

variable {W : Type*} [Fintype W]






/-- The true and false masses partition total prior mass. -/
lemma mass_split (μ : W → ℚ) (s : W → Bool) :
    trueMass μ s + falseMass μ s = ∑ ω, μ ω := by
  simp only [trueMass, falseMass]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  cases s ω <;> simp



/-- The always-false pure strategy's value. -/
theorem expOdds_zero (μ : W → ℚ) (s : W → Bool) (a b : ℚ) :
    expOdds μ s a b 0 = a * falseMass μ s - b * trueMass μ s := by
  rw [expOdds_eq]
  ring

/-- The always-true pure strategy's value. -/
theorem expOdds_one (μ : W → ℚ) (s : W → Bool) (a b : ℚ) :
    expOdds μ s a b 1 = a * trueMass μ s - b * falseMass μ s := by
  rw [expOdds_eq]
  ring

/-- Every randomized value is the convex affine combination of pure values. -/
theorem expOdds_affine (μ : W → ℚ) (s : W → Bool) (a b r : ℚ) :
    expOdds μ s a b r =
      r * expOdds μ s a b 1 + (1 - r) * expOdds μ s a b 0 := by
  rw [expOdds_eq, expOdds_eq, expOdds_eq]
  ring

/-- Randomization cannot beat the better pure strategy. -/
theorem no_benefit_randomization (μ : W → ℚ) (s : W → Bool) (a b r : ℚ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    expOdds μ s a b r ≤ max (expOdds μ s a b 0) (expOdds μ s a b 1) := by
  rw [expOdds_affine]
  calc r * expOdds μ s a b 1 + (1 - r) * expOdds μ s a b 0
      ≤ r * max (expOdds μ s a b 0) (expOdds μ s a b 1) + (1 - r) * max (expOdds μ s a b 0) (expOdds μ s a b 1) := by
        nlinarith [le_max_left (expOdds μ s a b 0) (expOdds μ s a b 1),
                   le_max_right (expOdds μ s a b 0) (expOdds μ s a b 1)]
    _ = max (expOdds μ s a b 0) (expOdds μ s a b 1) := by ring

/-- A positive randomized edge exists exactly when one pure bet has an edge. -/
theorem edge_iff_pure_edge (μ : W → ℚ) (s : W → Bool) (a b : ℚ) :
    (∃ r, 0 ≤ r ∧ r ≤ 1 ∧ 0 < expOdds μ s a b r) ↔
      0 < expOdds μ s a b 0 ∨ 0 < expOdds μ s a b 1 := by
  constructor
  · intro ⟨r, hr0, hr1, hrpos⟩
    have := no_benefit_randomization μ s a b r hr0 hr1
    have hmax : 0 < max (expOdds μ s a b 0) (expOdds μ s a b 1) := lt_of_lt_of_le hrpos this
    rw [lt_max_iff] at hmax
    exact hmax
  · intro h
    rcases h with h0 | h1
    · exact ⟨0, le_refl 0, by norm_num, h0⟩
    · exact ⟨1, by norm_num, le_refl 1, h1⟩

/-- Under a normalized prior, the pure-false value is `a-(a+b)π`. -/
theorem expOdds_zero_normalized (μ : W → ℚ) (s : W → Bool) (a b : ℚ)
    (hμ : ∑ ω, μ ω = 1) :
    expOdds μ s a b 0 = a - (a + b) * trueMass μ s := by
  rw [expOdds_zero]
  have hfalse : falseMass μ s = 1 - trueMass μ s := by
    linarith [mass_split μ s ▸ hμ]
  rw [hfalse]
  ring

/-- Under a normalized prior, the pure-true value is `(a+b)π-b`. -/
theorem expOdds_one_normalized (μ : W → ℚ) (s : W → Bool) (a b : ℚ)
    (hμ : ∑ ω, μ ω = 1) :
    expOdds μ s a b 1 = (a + b) * trueMass μ s - b := by
  rw [expOdds_one]
  have hfalse : falseMass μ s = 1 - trueMass μ s := by
    linarith [mass_split μ s]
  rw [hfalse]
  ring







open GodelCasinoAsymmetricOdds in
theorem solution(μ : W → ℚ) (s : W → Bool) (a b : ℚ)
    (hμ : ∑ ω, μ ω = 1) (hab : 0 < a + b) :
    (∃ r, 0 ≤ r ∧ r ≤ 1 ∧ 0 < expOdds μ s a b r) ↔
      trueMass μ s < a / (a + b) ∨ b / (a + b) < trueMass μ s := by
  rw [edge_iff_pure_edge]
  rw [expOdds_zero_normalized μ s a b hμ, expOdds_one_normalized μ s a b hμ]
  constructor
  · intro h
    rcases h with h0 | h1
    · left
      rw [lt_div_iff₀ hab]
      linarith
    · right
      rw [div_lt_iff₀ hab]
      linarith
  · intro h
    rcases h with h | h
    · left
      rw [lt_div_iff₀ hab] at h
      linarith
    · right
      rw [div_lt_iff₀ hab] at h
      linarith

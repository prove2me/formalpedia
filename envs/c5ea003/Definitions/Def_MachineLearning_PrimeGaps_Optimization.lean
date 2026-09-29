-- Prove2me | Definitions.Def_MachineLearning_PrimeGaps_Optimization
-- name    : MachineLearning_PrimeGaps_Optimization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:53:24.830591+00:00
-- url     : https://prove2.me/theorems/6346f0e8-c684-408f-adc2-742e8e8e7ab9
-- title:
--   Aether Catalog definitions — MachineLearning_PrimeGaps_Optimization
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.PrimeGaps.Optimization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/PrimeGaps/Optimization.lean by skeleton subtraction
import Mathlib
/-
# Finite-Dimensional Optimization Core of the Maynard Sieve

This file formalizes the exact extremal inequality S₂(w) ≤ k · S₁(w) where
S₁(w) = ∑ wᵢ² and S₂(w) = (∑ wᵢ)², and characterizes equality as holding
iff all weights are equal. This is the finite-dimensional positivity backbone
of the Maynard–Tao bounded gaps argument.

## Main results

* `sum_sq_le_card_mul_sq_sum` — The Cauchy–Schwarz inequality S₂ ≤ k·S₁
* `rayleigh_quotient_bound` — S₂/S₁ ≤ k with division
* `rayleigh_quotient_eq_iff_constant` — Equality iff all weights are equal
* `positiveWeightProfile_exists_iff` — The threshold existence theorem:
    ∃ w with S₂/S₁ > τ ⟺ τ < k
-/


open Finset BigOperators

/-- Sum of squares of weights. -/
def S1 {k : ℕ} (w : Fin k → ℝ) : ℝ := ∑ i, (w i) ^ 2

/-- Square of sum of weights. -/
def S2 {k : ℕ} (w : Fin k → ℝ) : ℝ := (∑ i, w i) ^ 2

/-
**Cauchy–Schwarz in finite dimension.** The square of the sum is at most
`k` times the sum of squares. This is the sharp finite-dimensional inequality
underlying Maynard-type weight optimization.
-/

/-
The Rayleigh quotient S₂/S₁ is bounded by k.
-/

/-
**Equality characterization.** S₂ = k·S₁ if and only if all weights are equal.
-/

/-- A weight profile beats threshold τ if S₂/S₁ > τ. -/
def PositiveWeightProfile {k : ℕ} (τ : ℝ) (w : Fin k → ℝ) : Prop :=
  S2 w / S1 w > τ

/-
**Threshold existence theorem.** There exists a weight vector with
S₂/S₁ > τ if and only if τ < k. This is the exact finite-dimensional
optimization threshold for the Maynard sieve.
-/



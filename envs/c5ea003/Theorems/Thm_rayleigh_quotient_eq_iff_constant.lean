-- Prove2me | Theorems.Thm_rayleigh_quotient_eq_iff_constant
-- name    : rayleigh_quotient_eq_iff_constant
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:02:33.03595+00:00
-- url     : https://prove2.me/theorems/29358d37-4b98-4eed-97c5-833e149d0da2
-- title:
--   Rayleigh quotient eq iff constant
-- statement:
--   Formal statement of `rayleigh_quotient_eq_iff_constant` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem rayleigh_quotient_eq_iff_constant{k : ℕ} (hk : 0 < k) (w : Fin k → ℝ) :
--       S2 w = k * S1 w ↔ ∃ c : ℝ, ∀ i, w i = c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PrimeGaps/Optimization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PrimeGaps/Optimization.lean#L53

-- Thm stub generated from MachineLearning/PrimeGaps/Optimization.lean
import Mathlib
import Definitions.Def_MachineLearning_PrimeGaps_Optimization
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

theorem rayleigh_quotient_eq_iff_constant{k : ℕ} (hk : 0 < k) (w : Fin k → ℝ) :
    S2 w = k * S1 w ↔ ∃ c : ℝ, ∀ i, w i = c := by sorry

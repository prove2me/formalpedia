-- Prove2me | Theorems.Thm_HalfPlane_four_pow_omega_dvd_circleCount
-- name    : HalfPlane.four_pow_omega_dvd_circleCount
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:23:01.754622+00:00
-- url     : https://prove2.me/theorems/ded6a51c-7cd5-4ca8-a892-42eb661b7d90
-- title:
--   A 2-adic constraint on the separable baseline.
-- statement:
--   **A 2-adic constraint on the separable baseline.**  For odd squarefree `N`,
--   `4^ω(N)` divides `C(N)`: every local factor `p - χ_p(-1)` is divisible by `4`,
--   since `p ≡ 1 (mod 4)` gives `4 ∣ p - 1` and `p ≡ 3 (mod 4)` gives `4 ∣ p + 1`.
--
--   ```lean
--   theorem HalfPlane.four_pow_omega_dvd_circleCount{N : ℕ} (hodd : ¬ 2 ∣ N) (hsq : Squarefree N) :
--       4 ^ N.primeFactors.card ∣ circleCount N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneClosedForm.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneClosedForm.lean#L68

-- Thm stub generated from MachineLearning/HalfPlaneClosedForm.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneClosedForm
import Definitions.Def_MachineLearning_HalfPlaneSemiprime

/-!
# Cycle 4: the separable baseline in closed form

The circle count is an arithmetic function in the technical sense, and it is
multiplicative.  Combined with the odd-prime conic count this gives a closed
product formula for every odd squarefree modulus:

  `C(N) = ∏_{p ∣ N} (p - χ_p(-1))`.

This is the exact "free-witness / CRT-separable" baseline: `C` is computable from the
factorisation of `N` in `O(ω(N))` arithmetic operations, while the non-separable
half-plane count `H` studied in the other files admits no such product formula
(`halfPlaneCount_not_multiplicative`).
-/

open HalfPlane

open Finset

theorem HalfPlane.four_pow_omega_dvd_circleCount{N : ℕ} (hodd : ¬ 2 ∣ N) (hsq : Squarefree N) :
    4 ^ N.primeFactors.card ∣ circleCount N := by sorry

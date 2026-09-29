-- Prove2me | Theorems.Thm_HalfPlane_circleCount_odd_squarefree
-- name    : HalfPlane.circleCount_odd_squarefree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:22:49.866451+00:00
-- url     : https://prove2.me/theorems/121d76d9-52d7-4ab3-8c16-c7c335ecd805
-- title:
--   Closed form of the separable baseline.
-- statement:
--   **Closed form of the separable baseline.**  For odd squarefree `N`,
--   `C(N) = ∏_{p ∣ N} (p - χ_p(-1))`, where the local factor is `p - 1` for
--   `p ≡ 1 (mod 4)` and `p + 1` for `p ≡ 3 (mod 4)`.
--
--   ```lean
--   theorem HalfPlane.circleCount_odd_squarefree{N : ℕ} (hodd : ¬ 2 ∣ N) (hsq : Squarefree N) :
--       circleCount N = ∏ p ∈ N.primeFactors, (if p % 4 = 1 then p - 1 else p + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneClosedForm.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneClosedForm.lean#L45

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

theorem HalfPlane.circleCount_odd_squarefree{N : ℕ} (hodd : ¬ 2 ∣ N) (hsq : Squarefree N) :
    circleCount N = ∏ p ∈ N.primeFactors, (if p % 4 = 1 then p - 1 else p + 1) := by sorry

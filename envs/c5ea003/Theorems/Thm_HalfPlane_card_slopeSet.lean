-- Prove2me | Theorems.Thm_HalfPlane_card_slopeSet
-- name    : HalfPlane.card_slopeSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:35:45.119361+00:00
-- url     : https://prove2.me/theorems/8acce86f-5e4b-4cc3-88ac-88e91f31e245
-- title:
--   The number of admissible slopes is `p - (χ(-1) + 1)`.
-- statement:
--   The number of admissible slopes is `p - (χ(-1) + 1)`.
--
--   ```lean
--   theorem HalfPlane.card_slopeSet(hp : p ≠ 2) :
--       ((slopeSet p).card : ℤ) = p - (quadraticChar (ZMod p) (-1) + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneCRTSeparable.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneCRTSeparable.lean#L163

-- Thm stub generated from MachineLearning/HalfPlaneCRTSeparable.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic

/-!
# The circle count is CRT-separable

The modular circle `x² + y² ≡ 1 (mod N)` is a *local* object: its point count
splits as a product over coprime factorisations,

  `C(m n) = C(m) · C(n)`  for `gcd(m,n) = 1`,

and at an odd prime it is given by the classical conic count

  `C(p) = p - χ(-1) = p - 1` if `p ≡ 1 (mod 4)`, `p + 1` if `p ≡ 3 (mod 4)`.

The proof of the prime formula is by the stereographic parametrisation of the
conic from the point `(-1, 0)`: the circle minus that point is in bijection with
the set of slopes `t` for which `1 + t² ≠ 0`.

This is the "CRT-separable" baseline against which the half-plane count
`H(N)` of `HalfPlaneReflection.lean` is measured.
-/

open HalfPlane

open Finset


variable {m n : ℕ} [NeZero m] [NeZero n]





variable (p : ℕ) [Fact (Nat.Prime p)]


variable {p}

theorem HalfPlane.card_slopeSet(hp : p ≠ 2) :
    ((slopeSet p).card : ℤ) = p - (quadraticChar (ZMod p) (-1) + 1) := by sorry

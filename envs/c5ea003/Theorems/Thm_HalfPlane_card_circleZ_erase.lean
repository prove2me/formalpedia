-- Prove2me | Theorems.Thm_HalfPlane_card_circleZ_erase
-- name    : HalfPlane.card_circleZ_erase
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:34:08.137412+00:00
-- url     : https://prove2.me/theorems/a1bd67d0-9fa6-458c-875c-513db4870e75
-- title:
--   Stereographic projection.
-- statement:
--   **Stereographic projection.** The circle minus `(-1,0)` is in bijection with the
--   set of slopes `t` satisfying `1 + t² ≠ 0`.
--
--   ```lean
--   theorem HalfPlane.card_circleZ_erase(hp : p ≠ 2) :
--       ((circleZ p).erase ((-1 : ZMod p), (0 : ZMod p))).card = (slopeSet p).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneCRTSeparable.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneCRTSeparable.lean#L113

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

theorem HalfPlane.card_circleZ_erase(hp : p ≠ 2) :
    ((circleZ p).erase ((-1 : ZMod p), (0 : ZMod p))).card = (slopeSet p).card := by sorry

-- Prove2me | Theorems.Thm_HalfPlane_circleCount_prime_int
-- name    : HalfPlane.circleCount_prime_int
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:35:51.273515+00:00
-- url     : https://prove2.me/theorems/65c8f360-0785-49bd-86ba-5aec8da7013a
-- title:
--   The circle count at an odd prime: `C(p) = p - χ(-1)`.
-- statement:
--   **The circle count at an odd prime**: `C(p) = p - χ(-1)`.
--
--   ```lean
--   theorem HalfPlane.circleCount_prime_int(hp : p ≠ 2) :
--       (circleCount p : ℤ) = (p : ℤ) - quadraticChar (ZMod p) (-1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneCRTSeparable.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneCRTSeparable.lean#L196

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

theorem HalfPlane.circleCount_prime_int(hp : p ≠ 2) :
    (circleCount p : ℤ) = (p : ℤ) - quadraticChar (ZMod p) (-1) := by sorry

-- Prove2me | Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
-- name    : MachineLearning_HalfPlaneCRTSeparable
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:41:24.357493+00:00
-- url     : https://prove2.me/theorems/f0bd72e5-4a42-4565-adb6-4b3d3ed83996
-- title:
--   Aether Catalog definitions — MachineLearning_HalfPlaneCRTSeparable
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.HalfPlaneCRTSeparable`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/HalfPlaneCRTSeparable.lean by skeleton subtraction
import Mathlib
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

namespace HalfPlane

open Finset

section CRT

variable {m n : ℕ} [NeZero m] [NeZero n]



end CRT

section Prime

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The set of admissible stereographic slopes: those `t` with `1 + t² ≠ 0`. -/
def slopeSet : Finset (ZMod p) := Finset.univ.filter (fun t => 1 + t ^ 2 ≠ 0)

variable {p}

instance : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩








end Prime

end HalfPlane



-- Prove2me | Definitions.Def_MachineLearning_HalfPlaneClosedForm
-- name    : MachineLearning_HalfPlaneClosedForm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T15:16:36.454692+00:00
-- url     : https://prove2.me/theorems/101835b8-e3fc-4f8e-8fa4-80b50c80ef0e
-- title:
--   Aether Catalog definitions — MachineLearning_HalfPlaneClosedForm
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.HalfPlaneClosedForm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/HalfPlaneClosedForm.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
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

namespace HalfPlane

open Finset

/-- The circle count packaged as an arithmetic function. -/
def circleArith : ArithmeticFunction ℕ where
  toFun := circleCount
  map_zero' := by decide





/-! ### Lab notes (cycle 4)

```
N = 15 = 3·5   : (3+1)(5-1) = 16 = C(15)   ✓
N = 21 = 3·7   : (3+1)(7+1) = 32 = C(21)   ✓
N = 35 = 5·7   : (5-1)(7+1) = 32 = C(35)   ✓
N = 105 = 3·5·7: (3+1)(5-1)(7+1) = 128     ✓
```
-/

end HalfPlane



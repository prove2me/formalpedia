-- Prove2me | Definitions.Def_MachineLearning_HalfPlaneParity
-- name    : MachineLearning_HalfPlaneParity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T15:19:31.075316+00:00
-- url     : https://prove2.me/theorems/530bcc09-5db5-42e5-bdb8-db2818cec09a
-- title:
--   Aether Catalog definitions — MachineLearning_HalfPlaneParity
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.HalfPlaneParity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/HalfPlaneParity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneSemiprime

/-!
# Cycle 3: the parity of the half-plane count is diagonal-local

The half-plane cut `x + y < N/2` is symmetric under the swap `(x,y) ↦ (y,x)`.
Consequently the parity of the non-separable count `H(N)` is decided entirely by
the *diagonal* solutions `x = y`, i.e. by the square roots of `1/2`:

  `H(N) ≡ #{x < N/4 : 2x² ≡ 1 (mod N)}  (mod 2)`.

Together with the reflection identity `H = high + 2R`, the same congruence holds
for the corner count `high(N)`.  So the non-separable object `H` is locally
determined *modulo 2*: any factor-dependent information it carries lives in its
higher-order bits.

We also record two sharpness facts:

* `exists_eight_mul_highCount_gt` : the constant `4` in `4·high(N) ≤ C(N)` cannot be
  improved to `8` (`N = 9`);
* `highCount_not_multiplicative` : the corner count is genuinely non-separable
  (`high(33) = 4` but `high(3)·high(11) = 0`).
-/

namespace HalfPlane

open Finset

/-- Diagonal points of the low half-plane: `x = y` forces `2x² ≡ 1 (mod N)` and
`4x < N`. -/
def fixDiagFinset (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun x => (2 * x ^ 2) % N = 1 % N ∧ 4 * x < N)

/-- The number of diagonal points of the low half-plane. -/
def fixDiagCount (N : ℕ) : ℕ := (fixDiagFinset N).card






/-! ### Sharpness and the genuine non-separability of the corner count -/



/-! ### Lab notes (cycle 3)

```
N     :  3  5  7  9 15 16 17 24 25 31 33 35
H(N)  :  2  2  2  4  4  6  3 12  6  7  8  6
diag  :  0  0  0  0  0  0  1  0  0  1  0  0
H mod 2: 0  0  0  0  0  0  1  0  0  1  0  0
```
The parity of `H` tracks the diagonal count exactly (checked by full enumeration
for all `N < 80`).  Note `N = 17`: `2·6² = 72 ≡ 4`, while `x = 3` gives
`2·9 = 18 ≡ 1 (mod 17)` and `4·3 = 12 < 17`, so the diagonal contributes one point
and `H(17) = 3` is odd.
-/

end HalfPlane



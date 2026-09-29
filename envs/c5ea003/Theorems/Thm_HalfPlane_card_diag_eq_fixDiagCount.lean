-- Prove2me | Theorems.Thm_HalfPlane_card_diag_eq_fixDiagCount
-- name    : HalfPlane.card_diag_eq_fixDiagCount
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:22:21.60531+00:00
-- url     : https://prove2.me/theorems/287c4d64-ad5f-4f23-9dd1-0993e4ced3e3
-- title:
--   The diagonal part of the low half-plane is parametrised by `x`.
-- statement:
--   The diagonal part of the low half-plane is parametrised by `x`.
--
--   ```lean
--   theorem HalfPlane.card_diag_eq_fixDiagCount(N : ℕ) :
--       ((lowFinset N).filter (fun p => p.1 = p.2)).card = fixDiagCount N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneParity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneParity.lean#L47

-- Thm stub generated from MachineLearning/HalfPlaneParity.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneParity
import Definitions.Def_MachineLearning_HalfPlaneReflection
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

open HalfPlane

open Finset

theorem HalfPlane.card_diag_eq_fixDiagCount(N : ℕ) :
    ((lowFinset N).filter (fun p => p.1 = p.2)).card = fixDiagCount N := by sorry

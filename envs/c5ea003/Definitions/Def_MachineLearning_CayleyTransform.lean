-- Prove2me | Definitions.Def_MachineLearning_CayleyTransform
-- name    : MachineLearning_CayleyTransform
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:38:12.439888+00:00
-- url     : https://prove2.me/theorems/ec9c2825-a9b9-4630-b320-b487c099e349
-- title:
--   Aether Catalog definitions — MachineLearning_CayleyTransform
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CayleyTransform`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CayleyTransform.lean by skeleton subtraction
import Mathlib

/-!
# Cayley Transform: Real Spectrum → Unit Circle

We prove that the Cayley transform `z = (w − i)/(w + i)` maps real numbers
to the unit circle. Combined with the fact that Hermitian matrices have real
eigenvalues, this gives: Hermitian spectra yield unit-circle zero sets after
Cayley transport.

## Main Results

- `cayley_of_real_on_unit_circle`: real `w` maps to `‖z‖ = 1` under Cayley transform
- `cayley_denom_ne_zero`: the denominator `w + i` is nonzero when `w` is real
-/

open Complex

noncomputable section

/-- The Cayley transform sending `ℝ` to the unit circle. -/
def cayleyTransform (w : ℂ) : ℂ :=
  (w - I) / (w + I)

/-
The denominator `w + i` is nonzero when `w` is real.
-/

/-
**Cayley transform of reals lands on the unit circle.**
    If `w` is real (i.e., `w.im = 0`), then `‖(w − i)/(w + i)‖ = 1`.
-/

end



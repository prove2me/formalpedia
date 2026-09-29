-- Prove2me | Definitions.Def_MachineLearning_NoiseFloor_EarlyStopping
-- name    : MachineLearning_NoiseFloor_EarlyStopping
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:49:42.244459+00:00
-- url     : https://prove2.me/theorems/b82f481e-137a-432d-bf8f-fa0e9045e481
-- title:
--   Aether Catalog definitions — MachineLearning_NoiseFloor_EarlyStopping
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.NoiseFloor.EarlyStopping`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/NoiseFloor/EarlyStopping.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
/-
# The Noise-Floor Principle, Part VII: early stopping versus ridge

Round-6 hypothesis closure, Phase A, cycle 4.

Gradient flow on a quadratic loss with data covariance spectrum `mu`, stopped at
time `tau`, is the spectral filter

  `gradFlowFilter mu tau i = 1 - exp (- mu i * tau)`,

the continuous-time idealisation of early stopping.  Folklore says "early
stopping is ridge with `lam = 1/tau`".  We make the folklore precise **and show
it is one-sided**:

* `gradFlow_le_four_mul_ridge` — early stopping at time `tau` is never worse
  than four times the matched ridge `lam = 1/tau`, for every spectrum, every
  signal and every noise level;
* `ridge_can_be_arbitrarily_worse` — the converse fails badly: on an explicit
  one-mode problem the matched ridge costs more than `100×` early stopping.

Both filters obey the Part II floor (`gradFlow_ge_noiseFloor`), so the
comparison is a statement about *how* the two families approach the same
irreducible limit: the exponential filter kills the bias of well-conditioned
modes at an exponential rate, while ridge only kills it polynomially.

## Main results

* `one_sub_exp_le_two_mul`   — `1 - e^{-u} ≤ 2u/(1+u)` (uniform in `u ≥ 0`)
* `exp_neg_le_one_div`       — `e^{-u} ≤ 1/(1+u)`
* `gradFlow_le_four_mul_ridge`, `gradFlow_ge_noiseFloor`
* `ridge_can_be_arbitrarily_worse`
-/

namespace Catalog.MachineLearning.NoiseFloor

open Finset

variable {ι : Type*} [Fintype ι]

/-- Gradient-flow (early stopping) spectral filter at time `tau`. -/
noncomputable def gradFlowFilter (mu : ι → ℝ) (tau : ℝ) : ι → ℝ :=
  fun i => 1 - Real.exp (-(mu i * tau))

section Scalar





end Scalar

section Comparison

variable {a mu : ι → ℝ} {b tau : ℝ}




end Comparison

section Separation



end Separation

end Catalog.MachineLearning.NoiseFloor



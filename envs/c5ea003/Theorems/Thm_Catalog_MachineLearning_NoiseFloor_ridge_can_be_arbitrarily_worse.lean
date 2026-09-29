-- Prove2me | Theorems.Thm_Catalog_MachineLearning_NoiseFloor_ridge_can_be_arbitrarily_worse
-- name    : Catalog.MachineLearning.NoiseFloor.ridge_can_be_arbitrarily_worse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:28:18.984648+00:00
-- url     : https://prove2.me/theorems/a144c230-2c05-417f-a2b8-25c28a67814b
-- title:
--   The converse fails: ridge can be dramatically worse than early stopping.
-- statement:
--   **The converse fails: ridge can be dramatically worse than early stopping.**
--   One mode, covariance eigenvalue `1`, signal power `a = e^{20}`, noise `b = 1`,
--   stopping time `tau = 10` and matched `lam = 1/10`.  Early stopping pays
--   `1 + (1 - e^{-10})^2 ≤ 2`, while ridge pays at least `e^{20}/121 ≥ 200`.
--
--   Hence the four-fold domination of `gradFlow_le_four_mul_ridge` is genuinely
--   one-sided: the exponential filter is the strictly better *family*, even though
--   both families are floored by the same `noiseFloor`.
--
--   ```lean
--   theorem Catalog.MachineLearning.NoiseFloor.ridge_can_be_arbitrarily_worse:
--       100 * filterRisk (fun _ : Fin 1 => Real.exp 20) 1 (gradFlowFilter (fun _ => 1) 10)
--         ≤ filterRisk (fun _ : Fin 1 => Real.exp 20) 1 (ridgeFilter (fun _ => 1) (1 / 10)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NoiseFloor/EarlyStopping.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NoiseFloor/EarlyStopping.lean#L158

-- Thm stub generated from MachineLearning/NoiseFloor/EarlyStopping.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EarlyStopping
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

open Catalog.MachineLearning.NoiseFloor

open Finset

variable {ι : Type*} [Fintype ι]









variable {a mu : ι → ℝ} {b tau : ℝ}

theorem Catalog.MachineLearning.NoiseFloor.ridge_can_be_arbitrarily_worse:
    100 * filterRisk (fun _ : Fin 1 => Real.exp 20) 1 (gradFlowFilter (fun _ => 1) 10)
      ≤ filterRisk (fun _ : Fin 1 => Real.exp 20) 1 (ridgeFilter (fun _ => 1) (1 / 10)) := by sorry

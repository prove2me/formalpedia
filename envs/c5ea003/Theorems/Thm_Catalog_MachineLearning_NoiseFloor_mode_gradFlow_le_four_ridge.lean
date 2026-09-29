-- Prove2me | Theorems.Thm_Catalog_MachineLearning_NoiseFloor_mode_gradFlow_le_four_ridge
-- name    : Catalog.MachineLearning.NoiseFloor.mode_gradFlow_le_four_ridge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:28:53.476615+00:00
-- url     : https://prove2.me/theorems/55fb0bab-3b8e-4c6c-9668-3833b5836e18
-- title:
--   Per-mode comparison of early stopping with matched ridge.
-- statement:
--   Per-mode comparison of early stopping with matched ridge.
--
--   ```lean
--   theorem Catalog.MachineLearning.NoiseFloor.mode_gradFlow_le_four_ridge{x b u : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) (hu : 0 ≤ u) :
--       x * (1 - (1 - Real.exp (-u))) ^ 2 + b * (1 - Real.exp (-u)) ^ 2
--         ≤ 4 * (x * (1 - u / (1 + u)) ^ 2 + b * (u / (1 + u)) ^ 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NoiseFloor/EarlyStopping.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NoiseFloor/EarlyStopping.lean#L80

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

theorem Catalog.MachineLearning.NoiseFloor.mode_gradFlow_le_four_ridge{x b u : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) (hu : 0 ≤ u) :
    x * (1 - (1 - Real.exp (-u))) ^ 2 + b * (1 - Real.exp (-u)) ^ 2
      ≤ 4 * (x * (1 - u / (1 + u)) ^ 2 + b * (u / (1 + u)) ^ 2) := by sorry

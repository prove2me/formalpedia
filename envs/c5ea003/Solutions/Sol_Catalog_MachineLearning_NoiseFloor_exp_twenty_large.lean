-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.exp_twenty_large
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:39:14.420517+00:00
-- url     : https://prove2.me/submissions/da0e975e-5242-4dfc-aafb-88dcde3f742b

-- Sol generated from MachineLearning/NoiseFloor/EarlyStopping.lean
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










open Catalog.MachineLearning.NoiseFloor in
theorem solution: (24200 : ℝ) ≤ Real.exp 20 := by
  have h1 : (2.718 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h2 : ((2.718 : ℝ)) ^ (20 : ℕ) ≤ (Real.exp 1) ^ (20 : ℕ) := by
    apply pow_le_pow_left₀ (by norm_num) h1.le
  have h3 : (Real.exp 1) ^ (20 : ℕ) = Real.exp 20 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h3] at h2
  have h4 : (24200 : ℝ) ≤ (2.718 : ℝ) ^ (20 : ℕ) := by norm_num
  linarith

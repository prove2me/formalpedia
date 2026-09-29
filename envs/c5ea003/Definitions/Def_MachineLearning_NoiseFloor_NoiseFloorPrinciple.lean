-- Prove2me | Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
-- name    : MachineLearning_NoiseFloor_NoiseFloorPrinciple
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:48:56.947015+00:00
-- url     : https://prove2.me/theorems/7cf7cab8-6bba-4a62-a7b0-a3d0cea5569c
-- title:
--   Aether Catalog definitions — MachineLearning_NoiseFloor_NoiseFloorPrinciple
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.NoiseFloor.NoiseFloorPrinciple`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/NoiseFloor/NoiseFloorPrinciple.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
/-
# The Noise-Floor Principle, Part II: the universal floor of spectral learning

Round-6 hypothesis closure, Phase A.

A *spectral filter* is the abstract form of every linear estimator that acts
diagonally in the eigenbasis of the data covariance: ridge regression, spectral
cut-off (PCA regression), gradient-flow early stopping, Tikhonov-type shrinkage,
kernel smoothing.  Writing `a i ≥ 0` for the signal power in mode `i` and `b > 0`
for the per-mode noise power (`b = σ²/N` in the usual fixed-design regression
normalisation), the excess risk of the filter `t : ι → ℝ` is

  `filterRisk a b t = ∑ i, (a i * (1 - t i)^2 + b * (t i)^2)`
                       ^^^^^^^^^^^^^^^^^^^      ^^^^^^^^^^^
                            bias                 variance

**The Noise-Floor Principle.** No spectral filter whatsoever — not just no ridge
parameter — can push the risk below

  `noiseFloor a b = b * effDim a b = ∑ i, a i * b / (a i + b)`,

and the bound is attained by exactly one filter, the Wiener filter
`t i = b / (a i + b)`.  Thus *the minimal achievable risk equals the noise level
times the effective dimension of the signal spectrum at that noise level*: the
trace functional of Part I is not merely an upper bound device, it is the exact
value of an optimisation problem.

## Main results

* `mode_gap_identity`        — the exact per-mode excess `((a+b)t - b)²/(a+b)`
* `filterRisk_ge_noiseFloor` — the noise-floor lower bound, for every filter
* `filterRisk_wiener`        — attainment by the Wiener filter
* `isLeast_filterRisk`       — the floor *is* the minimum of the risk functional
* `filterRisk_eq_noiseFloor_iff` — uniqueness of the optimal filter
* `noiseFloor_eq_sum`, `noiseFloor_le_min`, `half_count_le_noiseFloor`
* `noiseFloor_mono_level`, `noiseFloor_doubling` — the sample-size scaling law:
  the floor is monotone in the noise level and halving the data at most doubles it
* `ridge_optimal_iff_self_similar` — ridge attains the floor **iff** the spectrum
  satisfies the self-similarity relation `a i * μ i = b * λ` for all `i`
* `ridge_strict_gap_two_modes` — an explicit two-mode spectrum on which *every*
  ridge/constant filter is at least `4/3` times the floor: the frontier is strict.
-/

namespace Catalog.MachineLearning.NoiseFloor

open Finset

variable {ι : Type*} [Fintype ι]

/-- Excess risk of the diagonal (spectral) filter `t` against signal spectrum `a`
at noise level `b`: bias `a i (1 - t i)²` plus variance `b (t i)²`. -/
noncomputable def filterRisk (a : ι → ℝ) (b : ℝ) (t : ι → ℝ) : ℝ :=
  ∑ i, (a i * (1 - t i) ^ 2 + b * (t i) ^ 2)

/-- The Wiener (Bayes-optimal) filter for spectrum `a` at noise level `b`:
shrinkage by the per-mode signal-to-total ratio. -/
noncomputable def wienerFilter (a : ι → ℝ) (b : ℝ) : ι → ℝ := fun i => a i / (a i + b)

/-- The **noise floor**: noise level times effective dimension. -/
noncomputable def noiseFloor (a : ι → ℝ) (b : ℝ) : ℝ := b * effDim a b

/-- The ridge filter with regularisation `lam` for a covariance spectrum `mu`. -/
noncomputable def ridgeFilter (mu : ι → ℝ) (lam : ℝ) : ι → ℝ := fun i => mu i / (mu i + lam)

section Mode

variable {x b : ℝ}





end Mode

section Floor

variable {a : ι → ℝ} {b : ℝ}






end Floor

section Bounds

variable {a : ι → ℝ} {b : ℝ}








end Bounds

section Ridge

variable {a mu : ι → ℝ} {b lam : ℝ}








end Ridge

section Threshold

variable {b : ℝ}




end Threshold

end Catalog.MachineLearning.NoiseFloor



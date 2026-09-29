-- Prove2me | Theorems.Thm_Catalog_MachineLearning_NoiseFloor_filterRisk_eq_noiseFloor_iff
-- name    : Catalog.MachineLearning.NoiseFloor.filterRisk_eq_noiseFloor_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:27:56.946529+00:00
-- url     : https://prove2.me/theorems/13ece20e-7f85-4b97-a6c3-e0a3240ba648
-- title:
--   Uniqueness of the optimal filter.
-- statement:
--   **Uniqueness of the optimal filter.**  The Wiener filter is the *only*
--   minimiser; every other spectral filter is strictly suboptimal.
--
--   ```lean
--   theorem Catalog.MachineLearning.NoiseFloor.filterRisk_eq_noiseFloor_iff(ha : ∀ i, 0 ≤ a i) (hb : 0 < b) (t : ι → ℝ) :
--       filterRisk a b t = noiseFloor a b ↔ t = wienerFilter a b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NoiseFloor/NoiseFloorPrinciple.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NoiseFloor/NoiseFloorPrinciple.lean#L139

-- Thm stub generated from MachineLearning/NoiseFloor/NoiseFloorPrinciple.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
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

open Catalog.MachineLearning.NoiseFloor

open Finset

variable {ι : Type*} [Fintype ι]






variable {x b : ℝ}







variable {a : ι → ℝ} {b : ℝ}

theorem Catalog.MachineLearning.NoiseFloor.filterRisk_eq_noiseFloor_iff(ha : ∀ i, 0 ≤ a i) (hb : 0 < b) (t : ι → ℝ) :
    filterRisk a b t = noiseFloor a b ↔ t = wienerFilter a b := by sorry

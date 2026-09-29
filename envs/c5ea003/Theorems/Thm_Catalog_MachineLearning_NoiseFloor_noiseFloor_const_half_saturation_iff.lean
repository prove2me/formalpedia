-- Prove2me | Theorems.Thm_Catalog_MachineLearning_NoiseFloor_noiseFloor_const_half_saturation_iff
-- name    : Catalog.MachineLearning.NoiseFloor.noiseFloor_const_half_saturation_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:28:16.725312+00:00
-- url     : https://prove2.me/theorems/a3eb9e98-7526-4186-90ea-a680b3009fa7
-- title:
--   Sharp signal-to-noise threshold.
-- statement:
--   **Sharp signal-to-noise threshold.**  For a flat spectrum the floor reaches
--   half of its saturation value `n·b` exactly when the per-mode signal power reaches
--   the noise level: a genuine phase transition at SNR `= 1`.
--
--   ```lean
--   theorem Catalog.MachineLearning.NoiseFloor.noiseFloor_const_half_saturation_iff[Nonempty ι] (α : ℝ) (hα : 0 ≤ α) (hb : 0 < b) :
--       ((Fintype.card ι : ℝ) * b / 2 ≤ noiseFloor (fun _ : ι => α) b) ↔ b ≤ α := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NoiseFloor/NoiseFloorPrinciple.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NoiseFloor/NoiseFloorPrinciple.lean#L326

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








variable {a : ι → ℝ} {b : ℝ}










variable {a mu : ι → ℝ} {b lam : ℝ}










variable {b : ℝ}

theorem Catalog.MachineLearning.NoiseFloor.noiseFloor_const_half_saturation_iff[Nonempty ι] (α : ℝ) (hα : 0 ≤ α) (hb : 0 < b) :
    ((Fintype.card ι : ℝ) * b / 2 ≤ noiseFloor (fun _ : ι => α) b) ↔ b ≤ α := by sorry

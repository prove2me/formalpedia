-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.filterRisk_eq_noiseFloor_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:41:10.151282+00:00
-- url     : https://prove2.me/submissions/e67144e0-18ef-4bab-91f3-cfe967930d0f

-- Sol generated from MachineLearning/NoiseFloor/NoiseFloorPrinciple.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
import Theorems.Thm_Catalog_MachineLearning_NoiseFloor_noiseFloor_eq_sum
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

/-- **Exact per-mode gap identity.**  The whole principle rests on this completed
square: the risk of a mode exceeds `x b /(x + b)` by exactly
`((x+b) t - b)² / (x+b)`. -/
lemma mode_gap_identity (hx : 0 ≤ x) (hb : 0 < b) (t : ℝ) :
    x * (1 - t) ^ 2 + b * t ^ 2 - x * b / (x + b) = ((x + b) * t - x) ^ 2 / (x + b) := by
  have hd : 0 < x + b := by linarith
  field_simp
  ring

/-- Per-mode noise floor. -/
lemma mode_risk_ge (hx : 0 ≤ x) (hb : 0 < b) (t : ℝ) :
    x * b / (x + b) ≤ x * (1 - t) ^ 2 + b * t ^ 2 := by
  have hd : 0 < x + b := by linarith
  have h := mode_gap_identity hx hb t
  have : 0 ≤ ((x + b) * t - x) ^ 2 / (x + b) := by positivity
  linarith

/-- Per-mode attainment by the Wiener coefficient. -/
lemma mode_risk_wiener (hx : 0 ≤ x) (hb : 0 < b) :
    x * (1 - x / (x + b)) ^ 2 + b * (x / (x + b)) ^ 2 = x * b / (x + b) := by
  have hd : 0 < x + b := by linarith
  field_simp
  ring

/-- Off the Wiener coefficient the per-mode inequality is strict. -/
lemma mode_risk_gt (hx : 0 ≤ x) (hb : 0 < b) {t : ℝ} (ht : t ≠ x / (x + b)) :
    x * b / (x + b) < x * (1 - t) ^ 2 + b * t ^ 2 := by
  have hd : 0 < x + b := by linarith
  have hne : (x + b) * t - x ≠ 0 := by
    intro h
    apply ht
    field_simp
    linarith
  have hpos : 0 < ((x + b) * t - x) ^ 2 / (x + b) := by positivity
  have h := mode_gap_identity hx hb t
  linarith



variable {a : ι → ℝ} {b : ℝ}



/-- **Attainment.**  The Wiener filter meets the floor exactly. -/
theorem filterRisk_wiener (ha : ∀ i, 0 ≤ a i) (hb : 0 < b) :
    filterRisk a b (wienerFilter a b) = noiseFloor a b := by
  rw [noiseFloor_eq_sum, filterRisk]
  exact Finset.sum_congr rfl fun i _ => mode_risk_wiener (ha i) hb





variable {a : ι → ℝ} {b : ℝ}










variable {a mu : ι → ℝ} {b lam : ℝ}










variable {b : ℝ}






open Catalog.MachineLearning.NoiseFloor in
theorem solution(ha : ∀ i, 0 ≤ a i) (hb : 0 < b) (t : ι → ℝ) :
    filterRisk a b t = noiseFloor a b ↔ t = wienerFilter a b := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, t j ≠ wienerFilter a b j := by
      by_contra hall
      exact hne (funext fun i => not_not.1 fun hi => hall ⟨i, hi⟩)
    have hstrict : ∑ i, a i * b / (a i + b) < filterRisk a b t := by
      refine Finset.sum_lt_sum (fun i _ => mode_risk_ge (ha i) hb (t i)) ⟨j, mem_univ j, ?_⟩
      exact mode_risk_gt (ha j) hb hj
    rw [← noiseFloor_eq_sum, h] at hstrict
    exact lt_irrefl _ hstrict
  · rintro rfl
    exact filterRisk_wiener ha hb

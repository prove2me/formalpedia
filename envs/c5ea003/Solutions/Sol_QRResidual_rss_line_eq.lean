-- Prove2me | solution 1 for QRResidual.rss_line_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:26:32.072388+00:00
-- url     : https://prove2.me/submissions/693cb927-ee9d-4b20-9cc7-645d0d472f96

-- Sol generated from MachineLearning/QRResidual/ResidualLift.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_ResidualLift
import Theorems.Thm_QRResidual_le_rss
import Theorems.Thm_QRResidual_rss_le_of_mem
import Theorems.Thm_QRResidual_sqNorm_nonneg
import Theorems.Thm_QRResidual_sqNorm_sub_smul_eq

/-!
# Why a feature lifts R²: the exact residual-projection identity

Experiment 477 reports that adding the QR footprint feature to a fitted per-`N` yield
dial lifts the out-of-sample `R²` from `0.3927` to `0.5691`, and interprets this as a
refutation of the null hypothesis "H3: the residual contains nothing systematic".

This file supplies the exact optimisation theory behind that inference, for a finite
design (a finite sample of moduli).  Everything is elementary but exact: no asymptotics,
no distributional assumptions.

Main results.

* `sqNorm_sub_smul_eq` — the projection identity
  `‖r − t·v‖² = ‖r‖² − ⟨r,v⟩²/‖v‖²` at the optimal step `t = ⟨r,v⟩/‖v‖²`.
* `rss_mono` — enlarging the model class never increases the residual sum of squares
  (hence never decreases `R²`): `rsq_mono`.
* `rss_augment_le` — **quantitative lift**: augmenting a fit `g` by a feature `v`
  decreases the RSS by at least `⟨r,v⟩²/‖v‖²`, where `r = y − g` is the residual.
* `rsq_augment_ge`, `rsq_augment_strict` — the corresponding `R²` lift, and its
  strictness exactly when the residual correlates with the new feature.
* `residual_orthogonal_of_no_lift` — **the H3 dichotomy**: if augmenting by `v` produces
  no `R²` lift at all, then the residual is *exactly orthogonal* to `v`.  So an observed
  lift is not a fitting artefact: it is a certificate that the residual carried structure
  aligned with the feature.
-/

open QRResidual

open Finset

variable {ι : Type*} [Fintype ι]

/-! ## Finite-sample inner product -/





/-- Expansion of the squared norm along a step in the direction `v`. -/
theorem sqNorm_sub_smul (r v : ι → ℝ) (t : ℝ) :
    sqNorm (r - t • v) = sqNorm r - 2 * t * dot r v + t ^ 2 * sqNorm v := by
  simp only [sqNorm, dot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hpt : ∀ i : ι, (r i - t * v i) ^ 2
      = (r i) ^ 2 - 2 * t * (r i * v i) + t ^ 2 * (v i) ^ 2 := by
    intro i; ring
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]


/-! ## Residual sum of squares over a model class -/







/-- **Quantitative lift.**  If the class `T` contains the whole line `g + t·v`, then the
best fit in `T` beats the fit `g` by at least `⟨r,v⟩²/‖v‖²`, `r = y − g` the residual. -/
theorem rss_augment_le {y : ι → ℝ} {T : Set (ι → ℝ)} {g v : ι → ℝ}
    (hT : ∀ t : ℝ, g + t • v ∈ T) (hv : sqNorm v ≠ 0) :
    rss y T ≤ sqNorm (y - g) - (dot (y - g) v) ^ 2 / sqNorm v := by
  set r := y - g with hr
  set t := dot r v / sqNorm v with ht
  have hmem : g + t • v ∈ T := hT t
  have hrewrite : y - (g + t • v) = r - t • v := by
    funext i; simp [hr, Pi.sub_apply, Pi.add_apply]; ring
  calc rss y T ≤ sqNorm (y - (g + t • v)) := rss_le_of_mem hmem
    _ = sqNorm (r - t • v) := by rw [hrewrite]
    _ = sqNorm r - (dot r v) ^ 2 / sqNorm v := sqNorm_sub_smul_eq r v hv


/-! ## Exact optimum along one feature, and additivity of orthogonal features -/




/-! ## Coefficient of determination -/











open QRResidual in
theorem solution{y : ι → ℝ} {g v : ι → ℝ} (hv : sqNorm v ≠ 0) :
    rss y {h : ι → ℝ | ∃ t : ℝ, h = g + t • v}
      = sqNorm (y - g) - (dot (y - g) v) ^ 2 / sqNorm v := by
  have hs : 0 < sqNorm v := lt_of_le_of_ne (sqNorm_nonneg v) (Ne.symm hv)
  refine le_antisymm (rss_augment_le (fun t => ⟨t, rfl⟩) hv) ?_
  refine le_rss ⟨g, 0, by simp⟩ ?_
  rintro h ⟨t, rfl⟩
  have hrw : y - (g + t • v) = (y - g) - t • v := by
    funext i; simp [Pi.sub_apply, Pi.add_apply]; ring
  rw [hrw, sqNorm_sub_smul]
  have key : (dot (y - g) v) ^ 2 / sqNorm v
      ≥ 2 * t * dot (y - g) v - t ^ 2 * sqNorm v := by
    rw [ge_iff_le, le_div_iff₀ hs]
    nlinarith [sq_nonneg (dot (y - g) v - t * sqNorm v)]
  linarith

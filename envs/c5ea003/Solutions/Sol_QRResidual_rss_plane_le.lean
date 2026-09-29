-- Prove2me | solution 1 for QRResidual.rss_plane_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:26:32.556146+00:00
-- url     : https://prove2.me/submissions/303680a4-a519-4144-b6ed-894c2e01d62a

-- Sol generated from MachineLearning/QRResidual/ResidualLift.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_ResidualLift
import Theorems.Thm_QRResidual_rss_le_of_mem
import Theorems.Thm_QRResidual_sqNorm_nonneg

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







/-! ## Residual sum of squares over a model class -/









/-! ## Exact optimum along one feature, and additivity of orthogonal features -/


/-- Expansion of the residual energy along two directions. -/
theorem sqNorm_sub_two_smul (r v w : ι → ℝ) (t s : ℝ) :
    sqNorm (r - t • v - s • w)
      = sqNorm r - 2 * t * dot r v - 2 * s * dot r w + t ^ 2 * sqNorm v + s ^ 2 * sqNorm w
        + 2 * t * s * dot v w := by
  simp only [sqNorm, dot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have h : ∀ i : ι, (r i - t * v i - s * w i) ^ 2
      = (r i) ^ 2 - 2 * t * (r i * v i) - 2 * s * (r i * w i) + t ^ 2 * (v i) ^ 2
        + s ^ 2 * (w i) ^ 2 + 2 * t * s * (v i * w i) := by
    intro i; ring
  simp_rw [h]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]


/-! ## Coefficient of determination -/











open QRResidual in
theorem solution{y : ι → ℝ} {g v w : ι → ℝ} (hv : sqNorm v ≠ 0) (hw : sqNorm w ≠ 0)
    (hvw : dot v w = 0) :
    rss y {h : ι → ℝ | ∃ t s : ℝ, h = g + t • v + s • w}
      ≤ sqNorm (y - g) - (dot (y - g) v) ^ 2 / sqNorm v
          - (dot (y - g) w) ^ 2 / sqNorm w := by
  have hsv : 0 < sqNorm v := lt_of_le_of_ne (sqNorm_nonneg v) (Ne.symm hv)
  have hsw : 0 < sqNorm w := lt_of_le_of_ne (sqNorm_nonneg w) (Ne.symm hw)
  set r := y - g with hr
  set t := dot r v / sqNorm v with ht
  set s := dot r w / sqNorm w with hs
  have hmem : g + t • v + s • w ∈ {h : ι → ℝ | ∃ t s : ℝ, h = g + t • v + s • w} := ⟨t, s, rfl⟩
  have hrw : y - (g + t • v + s • w) = r - t • v - s • w := by
    funext i; simp [hr, Pi.sub_apply, Pi.add_apply]; ring
  calc rss y {h : ι → ℝ | ∃ t s : ℝ, h = g + t • v + s • w}
      ≤ sqNorm (y - (g + t • v + s • w)) := rss_le_of_mem hmem
    _ = sqNorm (r - t • v - s • w) := by rw [hrw]
    _ = sqNorm r - (dot r v) ^ 2 / sqNorm v - (dot r w) ^ 2 / sqNorm w := by
        rw [sqNorm_sub_two_smul, hvw, ht, hs]
        field_simp
        ring

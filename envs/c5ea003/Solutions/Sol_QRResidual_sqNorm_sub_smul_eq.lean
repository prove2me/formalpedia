-- Prove2me | solution 1 for QRResidual.sqNorm_sub_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:22:37.40297+00:00
-- url     : https://prove2.me/submissions/311bb11a-51f3-4ab1-96df-83143447e972

-- Sol generated from MachineLearning/QRResidual/ResidualLift.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_ResidualLift

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









/-! ## Exact optimum along one feature, and additivity of orthogonal features -/




/-! ## Coefficient of determination -/











open QRResidual in
theorem solution(r v : ι → ℝ) (hv : sqNorm v ≠ 0) :
    sqNorm (r - (dot r v / sqNorm v) • v) = sqNorm r - (dot r v) ^ 2 / sqNorm v := by
  rw [sqNorm_sub_smul]
  field_simp
  ring

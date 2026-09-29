-- Prove2me | solution 1 for QRResidual.rsq_augment_strict
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:24:53.252693+00:00
-- url     : https://prove2.me/submissions/41b92ca2-7d96-409f-b227-dc7c5426df5c

-- Sol generated from MachineLearning/QRResidual/ResidualLift.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_ResidualLift
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






/-- **Quantitative `R²` lift.**  Augmenting the fit `g` by the feature `v` raises `R²` by
at least `⟨r,v⟩² / (‖v‖² · TSS)`. -/
theorem rsq_augment_ge {y : ι → ℝ} {T : Set (ι → ℝ)} {g v : ι → ℝ}
    (hT : ∀ t : ℝ, g + t • v ∈ T) (hv : sqNorm v ≠ 0) (htss : 0 < tss y) :
    rsqOf y g + (dot (y - g) v) ^ 2 / (sqNorm v * tss y) ≤ rsq y T := by
  have h := rss_augment_le hT hv (y := y)
  have hdiv : rss y T / tss y
      ≤ (sqNorm (y - g) - (dot (y - g) v) ^ 2 / sqNorm v) / tss y :=
    (div_le_div_iff_of_pos_right htss).2 h
  unfold rsq rsqOf
  have hsplit : (sqNorm (y - g) - (dot (y - g) v) ^ 2 / sqNorm v) / tss y
      = sqNorm (y - g) / tss y - (dot (y - g) v) ^ 2 / (sqNorm v * tss y) := by
    field_simp
  linarith [hdiv, hsplit ▸ hdiv]





open QRResidual in
theorem solution{y : ι → ℝ} {T : Set (ι → ℝ)} {g v : ι → ℝ}
    (hT : ∀ t : ℝ, g + t • v ∈ T) (hv : sqNorm v ≠ 0) (htss : 0 < tss y)
    (hcorr : dot (y - g) v ≠ 0) : rsqOf y g < rsq y T := by
  have hpos : 0 < (dot (y - g) v) ^ 2 / (sqNorm v * tss y) := by
    have h1 : 0 < (dot (y - g) v) ^ 2 := by positivity
    have h2 : 0 < sqNorm v := lt_of_le_of_ne (sqNorm_nonneg v) (Ne.symm hv)
    exact div_pos h1 (by positivity)
  have := rsq_augment_ge hT hv htss (g := g) (v := v)
  linarith

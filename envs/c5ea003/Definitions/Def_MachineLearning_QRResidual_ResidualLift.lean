-- Prove2me | Definitions.Def_MachineLearning_QRResidual_ResidualLift
-- name    : MachineLearning_QRResidual_ResidualLift
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:53:34.345803+00:00
-- url     : https://prove2.me/theorems/ef14ee6d-a359-4b81-a1ae-301ec8ac5db8
-- title:
--   Aether Catalog definitions — MachineLearning_QRResidual_ResidualLift
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.QRResidual.ResidualLift`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/QRResidual/ResidualLift.lean by skeleton subtraction
import Mathlib

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

namespace QRResidual

open Finset

variable {ι : Type*} [Fintype ι]

/-! ## Finite-sample inner product -/

/-- Sample inner product of two feature vectors. -/
def dot (u v : ι → ℝ) : ℝ := ∑ i, u i * v i

/-- Sample squared norm. -/
def sqNorm (u : ι → ℝ) : ℝ := ∑ i, (u i) ^ 2





/-! ## Residual sum of squares over a model class -/

/-- Residual sum of squares of the best fit inside a class `S` of predictions. -/
noncomputable def rss (y : ι → ℝ) (S : Set (ι → ℝ)) : ℝ :=
  sInf ((fun g => sqNorm (y - g)) '' S)








/-! ## Exact optimum along one feature, and additivity of orthogonal features -/




/-! ## Coefficient of determination -/

/-- Sample mean of the response. -/
noncomputable def mean (y : ι → ℝ) : ℝ := (∑ i, y i) / (Fintype.card ι)

/-- Total sum of squares. -/
noncomputable def tss (y : ι → ℝ) : ℝ := sqNorm (y - fun _ => mean y)

/-- Coefficient of determination of the best fit in the class `S`. -/
noncomputable def rsq (y : ι → ℝ) (S : Set (ι → ℝ)) : ℝ := 1 - rss y S / tss y

/-- Coefficient of determination of a single given fit `g`. -/
noncomputable def rsqOf (y g : ι → ℝ) : ℝ := 1 - sqNorm (y - g) / tss y






end QRResidual



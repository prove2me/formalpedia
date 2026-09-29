-- Prove2me | Theorems.Thm_QRResidual_le_rss
-- name    : QRResidual.le_rss
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:50:37.637276+00:00
-- url     : https://prove2.me/theorems/6a4ff6e6-30dc-49d2-b4e1-bb7538a3f4d4
-- title:
--   A lower bound for the best fit: if every prediction in the class leaves at least `c`
-- statement:
--   A lower bound for the best fit: if every prediction in the class leaves at least `c`
--   of residual energy, then so does the optimum.
--
--   ```lean
--   theorem QRResidual.le_rss{y : ι → ℝ} {S : Set (ι → ℝ)} {c : ℝ} (hS : S.Nonempty)
--       (h : ∀ g ∈ S, c ≤ sqNorm (y - g)) : c ≤ rss y S := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/QRResidual/ResidualLift.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/QRResidual/ResidualLift.lean#L93

-- Thm stub generated from MachineLearning/QRResidual/ResidualLift.lean
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







/-! ## Residual sum of squares over a model class -/

theorem QRResidual.le_rss{y : ι → ℝ} {S : Set (ι → ℝ)} {c : ℝ} (hS : S.Nonempty)
    (h : ∀ g ∈ S, c ≤ sqNorm (y - g)) : c ≤ rss y S := by sorry

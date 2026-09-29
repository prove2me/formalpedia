-- Prove2me | Theorems.Thm_Logic_PhaseRoute_Rsq_additive_nonpos
-- name    : Logic.PhaseRoute.Rsq_additive_nonpos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:30:31.407988+00:00
-- url     : https://prove2.me/theorems/c02842fd-6e09-4f4d-87a2-aa5ccab8ab08
-- title:
--   **In `R²` units: the incremental gain of any singleton phase encoding is
-- statement:
--   **In `R²` units: the incremental gain of any singleton phase encoding is
--   `≤ 0`.**
--
--   ```lean
--   theorem Logic.PhaseRoute.Rsq_additive_nonpos(σ : α ≃ β) (hcard : 2 ≤ Fintype.card α) (u : α → ℝ) (v : β → ℝ) :
--       Rsq (graphInd σ) (additive u v) ≤ 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PhaseRouteAlignment.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PhaseRouteAlignment.lean#L252

-- Thm stub generated from Logic/PhaseRouteAlignment.lean
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
import Definitions.Def_Logic_PhaseRouteLeastSquares
/-
# The phase route is closed, but the interaction route is open — exactly

This file proves a *separation theorem* for feature encodings, in the exact
finite-sample least-squares calculus of `Logic.PhaseRouteLeastSquares`.

Setting.  The sample space is a product `α × β` (think: the residue of a root
position modulo one prime, paired with the residue modulo a second prime, or
paired with itself), and the target is an **alignment indicator**

  `graphInd σ (a, b) = if b = σ a then 1 else 0`   (`σ : α ≃ β`).

*Singleton* (linear-phase) encodings are the additive predictors
`additive u v (a, b) = u a + v b`, where `u`, `v` are **arbitrary** real
functions of a single coordinate — this is strictly more general than one-hot
dummies, sines/cosines of phases, or any other per-coordinate featurisation, and
it also covers arbitrarily many such features used simultaneously, since the
additive family is closed under sums.

Results.

* `cov_graphInd_additive_eq_zero` : every additive predictor has covariance
  *exactly* `0` with the alignment target.  There is no small residual signal to
  be found: the linear phase route is closed identically, not approximately.
* `graphInd_additive_no_gain` / `graphInd_additive_strict_loss` : consequently no
  additive predictor beats the intercept-only baseline, and every *nonconstant*
  one is strictly worse; the excess error equals the predictor's own variance.
* `Rsq_additive_nonpos` : the same statement in `R²` units — the attainable gain
  is `≤ 0`, never the pre-stated `+0.05`, and never even `+0.0215`.
* `nuisance_no_gain` : adding arbitrarily many features from an *independent*
  block of coordinates (other primes / other windows) does not change this.
* `graphInd_eq_sum_interactions` : the alignment target is *exactly* a sum of
  `card α` degree-2 products of one-hot singleton features, and
  `Rsq_interaction_eq_one` : that degree-2 encoding attains `R² = 1`.

So the missing variance is not merely hard to reach with singleton phases; it
lives, provably and entirely, in the degree-2 (joint alignment) layer.
-/

open Logic.PhaseRoute

open Finset

/-! ### Bilinearity tools for the empirical covariance -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]




/-! ### Products: lifting, and independence of distinct blocks -/

variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]







/-! ### Alignment targets and singleton (linear-phase) encodings -/

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α] [Nonempty β]

theorem Logic.PhaseRoute.Rsq_additive_nonpos(σ : α ≃ β) (hcard : 2 ≤ Fintype.card α) (u : α → ℝ) (v : β → ℝ) :
    Rsq (graphInd σ) (additive u v) ≤ 0 := by sorry

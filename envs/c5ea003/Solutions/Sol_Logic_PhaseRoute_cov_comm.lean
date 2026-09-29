-- Prove2me | solution 1 for Logic.PhaseRoute.cov_comm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:22:40.762101+00:00
-- url     : https://prove2.me/submissions/0c6ee8fb-e9d8-47a5-8d10-549f61a188a8

-- Sol generated from Logic/PhaseRouteAlignment.lean
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



















/-! ### Nuisance blocks: other primes, other windows, still nothing -/

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq β] [Nonempty α] [Nonempty β] [Nonempty γ]




/-! ### The interaction layer, where the missing variance actually lives -/

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  [Nonempty α] [Nonempty β]









/-! ### The prime windows `3 ≤ p ≤ 97`, concretely -/









open Logic.PhaseRoute in
omit [Nonempty ι] in
theorem solution(y h : ι → ℝ) : cov y h = cov h y := by
  have hfun : (fun i => y i * h i) = (fun i => h i * y i) := by funext i; ring
  simp only [cov, hfun]
  ring

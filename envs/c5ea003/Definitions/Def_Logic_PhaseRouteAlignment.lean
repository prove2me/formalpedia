-- Prove2me | Definitions.Def_Logic_PhaseRouteAlignment
-- name    : Logic_PhaseRouteAlignment
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:55:14.027506+00:00
-- url     : https://prove2.me/theorems/5b3ea699-2ae0-4088-82c2-0ebde74ef20d
-- title:
--   Aether Catalog definitions — Logic_PhaseRouteAlignment
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PhaseRouteAlignment`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PhaseRouteAlignment.lean by skeleton subtraction
import Mathlib
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

namespace Logic.PhaseRoute

open Finset

/-! ### Bilinearity tools for the empirical covariance -/

section Bilinear
variable {ι : Type*} [Fintype ι] [Nonempty ι]



end Bilinear

/-! ### Products: lifting, and independence of distinct blocks -/

section Product
variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]






end Product

/-! ### Alignment targets and singleton (linear-phase) encodings -/

section Alignment
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α] [Nonempty β]

/-- The alignment indicator of the bijection `σ`: the target is `1` exactly on
the graph of `σ`, i.e. exactly when the two coordinates are *jointly aligned*. -/
noncomputable def graphInd (σ : α ≃ β) : α × β → ℝ := fun x => if x.2 = σ x.1 then 1 else 0

/-- A singleton (linear-phase) predictor: an arbitrary function of the first
coordinate plus an arbitrary function of the second. -/
def additive (u : α → ℝ) (v : β → ℝ) : α × β → ℝ := fun x => u x.1 + v x.2
















end Alignment

/-! ### Nuisance blocks: other primes, other windows, still nothing -/

section Nuisance
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq β] [Nonempty α] [Nonempty β] [Nonempty γ]



end Nuisance

/-! ### The interaction layer, where the missing variance actually lives -/

section Interaction
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  [Nonempty α] [Nonempty β]

/-- One-hot singleton feature on the first coordinate. -/
noncomputable def onehotFst (c : α) : α × β → ℝ := fun x => if x.1 = c then 1 else 0

/-- One-hot singleton feature on the second coordinate. -/
noncomputable def onehotSnd (d : β) : α × β → ℝ := fun x => if x.2 = d then 1 else 0






end Interaction

/-! ### The prime windows `3 ≤ p ≤ 97`, concretely -/

section PrimeWindows

/-- Diagonal alignment of two root-position residues modulo `p`. -/
noncomputable def diagAlign (p : ℕ) [NeZero p] : ZMod p × ZMod p → ℝ :=
  graphInd (Equiv.refl (ZMod p))





end PrimeWindows

end Logic.PhaseRoute



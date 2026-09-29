-- Prove2me | Definitions.Def_Logic_PhaseRouteANOVA
-- name    : Logic_PhaseRouteANOVA
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:00:32.552981+00:00
-- url     : https://prove2.me/theorems/bb9d1754-a02f-4c8e-9c3a-d745cfb73098
-- title:
--   Aether Catalog definitions — Logic_PhaseRouteANOVA
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PhaseRouteANOVA`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PhaseRouteANOVA.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
import Definitions.Def_Logic_PhaseRouteLeastSquares
/-
# Where the excess lives: an exact degree-1 / degree-2 split of any target

`Logic.PhaseRouteAlignment` shows that one particular family of targets (the
alignment indicators) is invisible to every singleton encoding.  This file
proves the *structural* theorem behind it, for an arbitrary target on a product
sample space `α × β`:

  every `f : α × β → ℝ` splits **uniquely and orthogonally** as

      `f = addPart f + intPart f`,

  where `addPart f (a,b) = rowMean f a + colMean f b - avg f` is additive
  (degree `1`, i.e. reachable by singleton encodings) and `intPart f` has all
  row sums and all column sums equal to zero (degree `2`, pure interaction).

Main results.

* `intPart_zeroMarginals`, `cov_intPart_additive_eq_zero` : the interaction part
  is orthogonal to *every* additive predictor.
* `varr_split` : `varr f = varr (addPart f) + varr (intPart f)` — an exact
  variance budget with no cross term.
* `msse_additive_ge_varr_intPart` and `msse_addPart` : the best possible
  singleton model has error exactly `varr (intPart f)`, attained by `addPart f`.
* `Rsq_additive_le_ceiling` and `Rsq_addPart_eq_ceiling` : hence the **degree-1
  ceiling**

      `sup over singleton encodings of R² = varr (addPart f) / varr f`,

  which is a computable diagnostic: the entire unreachable excess is
  `varr (intPart f) / varr f`, no matter which singleton features are tried.
* `addPart_alignment_const` / `alignment_ceiling_zero` : for an alignment target
  the degree-1 part is *constant*, so its ceiling is `0` and the excess is
  `100%` — the closure result of `Logic.PhaseRouteAlignment` becomes a corollary
  of the general accounting identity.
-/

namespace Logic.PhaseRoute

open Finset

section ANOVA

variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]

/-- Row mean: average over the second coordinate with the first one fixed. -/
noncomputable def rowMean (f : α × β → ℝ) (a : α) : ℝ := avg (fun b : β => f (a, b))

/-- Column mean: average over the first coordinate with the second one fixed. -/
noncomputable def colMean (f : α × β → ℝ) (b : β) : ℝ := avg (fun a : α => f (a, b))

/-- The degree-1 (additive, "singleton-reachable") part of `f`. -/
noncomputable def addPart (f : α × β → ℝ) : α × β → ℝ :=
  additive (fun a => rowMean f a) (fun b => colMean f b - avg f)

/-- The degree-2 (pure interaction) part of `f`. -/
noncomputable def intPart (f : α × β → ℝ) : α × β → ℝ := fun x => f x - addPart f x



















end ANOVA

/-! ### The alignment target has degree-1 ceiling exactly zero -/

section AlignmentCeiling

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α] [Nonempty β]






end AlignmentCeiling

end Logic.PhaseRoute



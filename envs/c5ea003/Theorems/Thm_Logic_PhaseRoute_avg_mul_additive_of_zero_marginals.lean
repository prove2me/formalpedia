-- Prove2me | Theorems.Thm_Logic_PhaseRoute_avg_mul_additive_of_zero_marginals
-- name    : Logic.PhaseRoute.avg_mul_additive_of_zero_marginals
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:30:44.938672+00:00
-- url     : https://prove2.me/theorems/c72e84ea-0550-431d-8f09-ba4ed6207909
-- title:
--   A function with vanishing row and column sums is orthogonal to every additive
-- statement:
--   A function with vanishing row and column sums is orthogonal to every additive
--   predictor: the raw mean of the product already vanishes.
--
--   ```lean
--   theorem Logic.PhaseRoute.avg_mul_additive_of_zero_marginals{g : α × β → ℝ}
--       (hrow : ∀ a, (∑ b : β, g (a, b)) = 0) (hcol : ∀ b, (∑ a : α, g (a, b)) = 0)
--       (u : α → ℝ) (v : β → ℝ) :
--       avg (fun x : α × β => g x * additive u v x) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PhaseRouteANOVA.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PhaseRouteANOVA.lean#L130

-- Thm stub generated from Logic/PhaseRouteANOVA.lean
import Mathlib
import Definitions.Def_Logic_PhaseRouteANOVA
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

open Logic.PhaseRoute

open Finset


variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]














omit [Nonempty α] [Nonempty β] in

theorem Logic.PhaseRoute.avg_mul_additive_of_zero_marginals{g : α × β → ℝ}
    (hrow : ∀ a, (∑ b : β, g (a, b)) = 0) (hcol : ∀ b, (∑ a : α, g (a, b)) = 0)
    (u : α → ℝ) (v : β → ℝ) :
    avg (fun x : α × β => g x * additive u v x) = 0 := by sorry

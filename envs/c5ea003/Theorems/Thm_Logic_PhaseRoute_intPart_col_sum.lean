-- Prove2me | Theorems.Thm_Logic_PhaseRoute_intPart_col_sum
-- name    : Logic.PhaseRoute.intPart_col_sum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:31:19.668078+00:00
-- url     : https://prove2.me/theorems/b519e970-bdaf-4579-b849-899a1db2ff48
-- title:
--   Each column of the interaction part sums to zero.
-- statement:
--   Each column of the interaction part sums to zero.
--
--   ```lean
--   theorem Logic.PhaseRoute.intPart_col_sum(f : α × β → ℝ) (b : β) : (∑ a : α, intPart f (a, b)) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PhaseRouteANOVA.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PhaseRouteANOVA.lean#L114

-- Thm stub generated from Logic/PhaseRouteANOVA.lean
import Mathlib
import Definitions.Def_Logic_PhaseRouteANOVA
import Definitions.Def_Logic_PhaseRouteAlignment
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

theorem Logic.PhaseRoute.intPart_col_sum(f : α × β → ℝ) (b : β) : (∑ a : α, intPart f (a, b)) = 0 := by sorry

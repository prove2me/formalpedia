-- Prove2me | Definitions.Def_MachineLearning_BonferroniMarginals_MarginalIndeterminacy
-- name    : MachineLearning_BonferroniMarginals_MarginalIndeterminacy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:36:59.976833+00:00
-- url     : https://prove2.me/theorems/44bc6036-078f-4a06-bb9d-7a6ff2724640
-- title:
--   Aether Catalog definitions — MachineLearning_BonferroniMarginals_MarginalIndeterminacy
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.BonferroniMarginals.MarginalIndeterminacy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/BonferroniMarginals/MarginalIndeterminacy.lean by skeleton subtraction
import Mathlib

/-!
# The marginal-order dichotomy: second-order data does not determine the union

The Bonferroni machinery of `Core.lean` consumes only **first- and second-order
marginals** of a family: the numbers `|Aᵢ|` and `|Aᵢ ∩ Aⱼ|`.  This file settles
the natural question raised by that observation: *could any cleverer argument,
still using only those numbers, compute the union exactly?*

The answer is **no**, and the obstruction is explicit and tiny.

* `triangle` and `sunflower` are two families of three `2`-element subsets of a
  `4`-element sample space with **identical** first and second marginals
  (`|Aᵢ| = 2`, `|Aᵢ ∩ Aⱼ| = 1` for `i ≠ j`) and **different** unions
  (`3` versus `4`).
* `union_not_determined_by_second_order_marginals` — hence no function of the
  second-order marginal data computes the union cardinality
  (`no_second_order_formula`).
* `card_cover_eq_of_all_inf_card_eq` — the positive counterpart: the *full*
  intersection data (all orders) does determine the union, by inclusion–exclusion.
  For three sets, order `3` suffices and order `2` does not, so the threshold is
  sharp on this example.
* `triangle_corradi_tight` / `sunflower_corradi_strict` — the same pair of
  families shows that the Corrádi bound of `Corradi.lean` is *exactly* the best
  bound expressible in `(k, m, t)`: the triangle attains it, the sunflower is
  strictly above it.
* `sunflower_doubleCollision_strict` — and the double-collision bound is strict
  exactly because the sunflower has a point of multiplicity `3`, as predicted by
  `doubleCollision_tight_iff`.

Machine-learning reading: knowing every individual error rate and every pairwise
error correlation of an ensemble is provably insufficient to know the ensemble's
total error support; the missing information is a genuine higher-order
interaction.
-/

namespace BonferroniMarginals

open Finset

/-! ## The two witness families -/

/-- Three `2`-element sets forming a triangle: `{0,1}, {1,2}, {2,0}`. -/
def triangle : Fin 3 → Finset (Fin 4)
  | 0 => {0, 1}
  | 1 => {1, 2}
  | 2 => {2, 0}

/-- Three `2`-element sets forming a sunflower with core `{0}`:
`{0,1}, {0,2}, {0,3}`. -/
def sunflower : Fin 3 → Finset (Fin 4)
  | 0 => {0, 1}
  | 1 => {0, 2}
  | 2 => {0, 3}







/-! ## The no-go theorem -/



/-! ## The positive counterpart: all orders suffice -/


/-! ## What this says about the quantitative bounds -/







end BonferroniMarginals



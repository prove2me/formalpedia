-- Prove2me | Theorems.Thm_BonferroniMarginals_mult_eq_one_of_not_doubleCollision
-- name    : BonferroniMarginals.mult_eq_one_of_not_doubleCollision
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:26:29.765318+00:00
-- url     : https://prove2.me/theorems/658e2986-a272-4582-96f4-2c586c60f838
-- title:
--   A point of the cover which is not a double collision lies in exactly one member.
-- statement:
--   A point of the cover which is not a double collision lies in exactly one member.
--
--   ```lean
--   theorem BonferroniMarginals.mult_eq_one_of_not_doubleCollision{x : Ω} (hx : x ∈ cover I A)
--       (hx2 : x ∉ doubleCollision I A) : mult I A x = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/BonferroniMarginals/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/BonferroniMarginals/Core.lean#L198

-- Thm stub generated from MachineLearning/BonferroniMarginals/Core.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core

/-!
# The Bonferroni machinery: multiplicity calculus for arbitrary finite families

This file builds, from scratch and for an *arbitrary* finite family
`A : ι → Finset Ω` indexed by a finite set `I : Finset ι`, the exact
book-keeping that underlies every Bonferroni-type inequality.

The organising object is the **multiplicity** (or *degree*, or *coverage
count*) function
`mult I A x = #{i ∈ I | x ∈ A i}`.
All first- and second-order *marginals* of the family are moments of `mult`
on the cover `⋃ i ∈ I, A i`:

* `sum_mult_eq_sum_card` : `∑ₓ mult x = ∑ᵢ |Aᵢ|`  (first marginal moment)
* `sum_mult_sq_eq_sum_prod` : `∑ₓ (mult x)² = ∑_{(i,j)} |Aᵢ ∩ Aⱼ|` (second)
* `sum_offDiag_eq` : the off-diagonal part is `∑ₓ mult x * (mult x - 1)`.

From these two identities the whole machinery follows:

* `card_sum_le_card_biUnion_add_offDiag` — the **second Bonferroni inequality**
  in its off-diagonal (unordered-pair-free) form.
* `card_doubleCollision_mul_le` — the **double-collision bound**: twice the
  number of points covered at least twice is at most the pairwise-overlap mass.
* `sq_sum_card_le_card_cover_mul_sum_prod` — the **Cauchy–Schwarz upgrade**
  `(∑ᵢ |Aᵢ|)² ≤ |cover| · ∑_{(i,j)} |Aᵢ ∩ Aⱼ|`, which is strictly stronger than
  Bonferroni whenever the family is far from a partition.

Machine-learning reading: `Ω` is a finite sample space, `A i` the set of samples
on which hypothesis `i` fails (its *bad event*), `|A i|` the first marginal,
`|A i ∩ A j|` the second.  `mult` is the number of ensemble members that fail
at a given sample, `cover` is the set of samples on which the ensemble is not
unanimously correct, and `doubleCollision` is the set of samples where the
failures are *correlated*.
-/

open BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω]
variable {I : Finset ι} {A : ι → Finset Ω}

/-! ## The multiplicity function -/









/-! ## The two moment identities -/







/-! ## The Bonferroni machinery -/

theorem BonferroniMarginals.mult_eq_one_of_not_doubleCollision{x : Ω} (hx : x ∈ cover I A)
    (hx2 : x ∉ doubleCollision I A) : mult I A x = 1 := by sorry

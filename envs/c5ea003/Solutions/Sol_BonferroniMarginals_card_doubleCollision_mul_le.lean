-- Prove2me | solution 1 for BonferroniMarginals.card_doubleCollision_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:23:51.645454+00:00
-- url     : https://prove2.me/submissions/9968d3a8-03e6-4094-86e7-40a4fa63855c

-- Sol generated from MachineLearning/BonferroniMarginals/Core.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Theorems.Thm_BonferroniMarginals_sum_offDiag_eq

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




/-! ## The Cauchy–Schwarz upgrade

The Bonferroni inequality uses the pointwise bound `2d ≤ 1 + d²`.  Summing the
*sharp* Cauchy–Schwarz inequality instead gives a bound that is strictly
stronger for families that are far from a partition. -/




open BonferroniMarginals in
theorem solution[DecidableEq ι] (I : Finset ι) (A : ι → Finset Ω) :
    2 * (doubleCollision I A).card ≤ ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card := by
  rw [sum_offDiag_eq]
  have hsub : doubleCollision I A ⊆ cover I A := Finset.filter_subset _ _
  calc 2 * (doubleCollision I A).card
      = ∑ x ∈ doubleCollision I A, 2 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ doubleCollision I A, (mult I A x) * (mult I A x - 1) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have h2 : 2 ≤ mult I A x := (Finset.mem_filter.mp hx).2
        have : 1 ≤ mult I A x - 1 := by omega
        calc (2:ℕ) = 2 * 1 := by ring
          _ ≤ mult I A x * (mult I A x - 1) := Nat.mul_le_mul h2 this
    _ ≤ ∑ x ∈ cover I A, (mult I A x) * (mult I A x - 1) :=
        Finset.sum_le_sum_of_subset hsub

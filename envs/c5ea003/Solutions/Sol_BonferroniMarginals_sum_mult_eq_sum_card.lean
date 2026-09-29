-- Prove2me | solution 1 for BonferroniMarginals.sum_mult_eq_sum_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:16:03.246475+00:00
-- url     : https://prove2.me/submissions/5a9f0274-2a97-4111-9243-55ab790fc851

-- Sol generated from MachineLearning/BonferroniMarginals/Core.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Theorems.Thm_BonferroniMarginals_mem_cover

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







lemma subset_cover {i : ι} (hi : i ∈ I) : A i ⊆ cover I A := fun _ hx =>
  mem_cover.mpr ⟨i, hi, hx⟩

/-- The multiplicity is the sum of the indicator marginals. -/
lemma mult_eq_sum_indicator (x : Ω) :
    mult I A x = ∑ i ∈ I, if x ∈ A i then 1 else 0 := by
  rw [mult, Finset.card_filter]

/-! ## The two moment identities -/

/-- **First moment identity.** Summing the multiplicity over any set containing the
cover recovers the sum of the first marginals `|Aᵢ|`. -/
lemma sum_mult_eq_sum_card_of_subset (S : Finset Ω) (hS : ∀ i ∈ I, A i ⊆ S) :
    ∑ x ∈ S, mult I A x = ∑ i ∈ I, (A i).card := by
  simp only [mult_eq_sum_indicator]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.card_filter]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hS i hi)]






/-! ## The Bonferroni machinery -/




/-! ## The Cauchy–Schwarz upgrade

The Bonferroni inequality uses the pointwise bound `2d ≤ 1 + d²`.  Summing the
*sharp* Cauchy–Schwarz inequality instead gives a bound that is strictly
stronger for families that are far from a partition. -/




open BonferroniMarginals in
theorem solution(I : Finset ι) (A : ι → Finset Ω) :
    ∑ x ∈ cover I A, mult I A x = ∑ i ∈ I, (A i).card :=
  sum_mult_eq_sum_card_of_subset _ fun _ hi => subset_cover hi

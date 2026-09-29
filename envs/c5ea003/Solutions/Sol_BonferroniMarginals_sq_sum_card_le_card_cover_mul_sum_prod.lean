-- Prove2me | solution 1 for BonferroniMarginals.sq_sum_card_le_card_cover_mul_sum_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:22:18.551012+00:00
-- url     : https://prove2.me/submissions/7f6da0c1-552b-4e34-bcc0-d5cf69faeb38

-- Sol generated from MachineLearning/BonferroniMarginals/Core.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Theorems.Thm_BonferroniMarginals_lagrange_identity
import Theorems.Thm_BonferroniMarginals_sum_mult_eq_sum_card
import Theorems.Thm_BonferroniMarginals_sum_mult_sq_eq_sum_prod

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
theorem solution(I : Finset ι) (A : ι → Finset Ω) :
    (∑ i ∈ I, (A i).card) ^ 2
      ≤ (cover I A).card * ∑ p ∈ I ×ˢ I, (A p.1 ∩ A p.2).card := by
  have hL := lagrange_identity (cover I A) (fun x => (mult I A x : ℤ))
  have hnn : (0:ℤ) ≤ ∑ x ∈ cover I A, ∑ y ∈ cover I A,
      ((mult I A x : ℤ) - (mult I A y : ℤ)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← hL] at hnn
  have h1 : ((∑ x ∈ cover I A, mult I A x : ℕ) : ℤ) = ∑ x ∈ cover I A, (mult I A x : ℤ) := by
    push_cast; ring
  have h2 : ((∑ x ∈ cover I A, (mult I A x) ^ 2 : ℕ) : ℤ)
      = ∑ x ∈ cover I A, (mult I A x : ℤ) ^ 2 := by push_cast; ring
  have hkey : ((∑ x ∈ cover I A, mult I A x : ℕ) : ℤ) ^ 2
      ≤ ((cover I A).card : ℤ) * ((∑ x ∈ cover I A, (mult I A x) ^ 2 : ℕ) : ℤ) := by
    rw [h1, h2]; linarith
  rw [sum_mult_eq_sum_card, sum_mult_sq_eq_sum_prod] at hkey
  exact_mod_cast hkey

-- Prove2me | solution 1 for BonferroniMarginals.bonferroni_tight_iff_mult_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:21:00.763133+00:00
-- url     : https://prove2.me/submissions/3f7a9e10-6c33-4b37-bb6d-a525b30929ae

-- Sol generated from MachineLearning/BonferroniMarginals/Rigidity.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_Rigidity
import Theorems.Thm_BonferroniMarginals_one_le_mult_of_mem_cover
import Theorems.Thm_BonferroniMarginals_sum_mult_eq_sum_card
import Theorems.Thm_BonferroniMarginals_sum_offDiag_eq

/-!
# Rigidity: exactly how much the Bonferroni machinery loses

`Core.lean` proves the two Bonferroni-type inequalities for an arbitrary finite
family.  This file identifies their **defect** exactly, and characterises the
families that make each of them an equality.  The slogan is:

> Every Bonferroni inequality is an identity plus a nonnegative *irregularity*
> functional of the multiplicity function; the inequality is tight precisely on
> the families whose irregularity vanishes.

Main results.

* `bonferroni_defect_identity` — the exact identity
  `∑ᵢ|Aᵢ| + ∑ₓ (mult x − 1)² = |cover| + ∑_{i≠j}|Aᵢ ∩ Aⱼ|`.
  The Bonferroni slack is the total squared deviation of the coverage
  multiplicity from `1`.
* `bonferroni_tight_iff_mult_one`, `bonferroni_tight_iff_pairwiseDisjoint` —
  the second Bonferroni inequality is an equality **iff** the family is pairwise
  disjoint.
* `doubleCollision_tight_iff` — the double-collision bound is an equality **iff**
  no point is covered three times: the machinery is sharp exactly on families of
  *bounded multiplicity 2*.
* `cauchySchwarz_tight_iff_regular` — the Cauchy–Schwarz (Corrádi) bound is an
  equality **iff** the cover is *regular*, i.e. the multiplicity is constant.

Machine-learning reading: the Bonferroni union bound is lossless exactly for
ensembles whose failure sets never overlap, and the second-order Corrádi bound
is lossless exactly for ensembles whose failures are spread perfectly evenly
over the sample space — a formal statement of "the union bound is tight iff the
errors are uncorrelated, the second-moment bound is tight iff they are equally
correlated".
-/

open BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω]
variable {I : Finset ι} {A : ι → Finset Ω}

/-! ## Regular covers -/



/-! ## The exact Bonferroni defect -/

/-- **The Bonferroni defect identity.**  For every finite family,
`∑ᵢ |Aᵢ| + ∑ₓ (mult x − 1)² = |⋃ᵢ Aᵢ| + ∑_{i ≠ j} |Aᵢ ∩ Aⱼ|`.

Since the middle term is a sum of squares, this refines
`card_sum_le_card_biUnion_add_offDiag` into an equality and exhibits the loss of
the Bonferroni inequality as the *irregularity* `∑ₓ (mult x − 1)²`. -/
theorem bonferroni_defect_identity [DecidableEq ι] (I : Finset ι) (A : ι → Finset Ω) :
    ∑ i ∈ I, (A i).card + ∑ x ∈ cover I A, (mult I A x - 1) ^ 2
      = (cover I A).card + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card := by
  rw [sum_offDiag_eq, ← sum_mult_eq_sum_card, ← Finset.sum_add_distrib]
  rw [show (cover I A).card = ∑ _x ∈ cover I A, 1 by simp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (one_le_mult_of_mem_cover hx)
  rw [hk, show 1 + k - 1 = k by omega]
  ring




/-! ## Tightness of the double-collision bound -/


/-! ## Tightness of the Cauchy–Schwarz (Corrádi) bound -/




open BonferroniMarginals in
theorem solution[DecidableEq ι] (I : Finset ι) (A : ι → Finset Ω) :
    (∑ i ∈ I, (A i).card = (cover I A).card + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card)
      ↔ ∀ x ∈ cover I A, mult I A x = 1 := by
  have hid := bonferroni_defect_identity I A
  constructor
  · intro heq
    have hzero : ∑ x ∈ cover I A, (mult I A x - 1) ^ 2 = 0 := by omega
    intro x hx
    have h1 := one_le_mult_of_mem_cover hx
    have hterm := (Finset.sum_eq_zero_iff.mp hzero) x hx
    have hsq : mult I A x - 1 = 0 := by simpa using hterm
    omega
  · intro hone
    have hzero : ∑ x ∈ cover I A, (mult I A x - 1) ^ 2 = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [hone x hx]; simp
    omega

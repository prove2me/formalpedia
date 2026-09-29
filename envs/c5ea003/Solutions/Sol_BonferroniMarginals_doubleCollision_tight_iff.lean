-- Prove2me | solution 1 for BonferroniMarginals.doubleCollision_tight_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:25:25.054001+00:00
-- url     : https://prove2.me/submissions/3e7e0556-a285-42c6-8009-778fe4d0b018

-- Sol generated from MachineLearning/BonferroniMarginals/Rigidity.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_Rigidity
import Theorems.Thm_BonferroniMarginals_mult_eq_one_of_not_doubleCollision
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





/-! ## Tightness of the double-collision bound -/


/-! ## Tightness of the Cauchy–Schwarz (Corrádi) bound -/




open BonferroniMarginals in
theorem solution[DecidableEq ι] (I : Finset ι) (A : ι → Finset Ω) :
    (2 * (doubleCollision I A).card = ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card)
      ↔ ∀ x ∈ cover I A, mult I A x ≤ 2 := by
  classical
  have hsub : doubleCollision I A ⊆ cover I A := Finset.filter_subset _ _
  have hrestrict : ∑ x ∈ cover I A, (mult I A x) * (mult I A x - 1)
      = ∑ x ∈ doubleCollision I A, (mult I A x) * (mult I A x - 1) := by
    refine (Finset.sum_subset hsub ?_).symm
    intro x hx hxn
    have := mult_eq_one_of_not_doubleCollision hx hxn
    simp [this]
  have hkey : (2 * (doubleCollision I A).card
      = ∑ x ∈ doubleCollision I A, (mult I A x) * (mult I A x - 1))
      ↔ ∀ x ∈ doubleCollision I A, mult I A x = 2 := by
    rw [show 2 * (doubleCollision I A).card = ∑ _x ∈ doubleCollision I A, 2 by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]]
    rw [Finset.sum_eq_sum_iff_of_le (fun x hx => ?_)]
    · constructor
      · intro h x hx
        have h2 : 2 ≤ mult I A x := (Finset.mem_filter.mp hx).2
        have := h x hx
        nlinarith [this, h2, Nat.sub_add_cancel (show 1 ≤ mult I A x by omega)]
      · intro h x hx
        rw [h x hx]
    · have h2 : 2 ≤ mult I A x := (Finset.mem_filter.mp hx).2
      calc (2:ℕ) = 2 * 1 := by ring
        _ ≤ mult I A x * (mult I A x - 1) := Nat.mul_le_mul h2 (by omega)
  rw [sum_offDiag_eq, hrestrict, hkey]
  constructor
  · intro h x hx
    by_cases hx2 : x ∈ doubleCollision I A
    · exact le_of_eq (h x hx2)
    · exact le_of_eq_of_le (mult_eq_one_of_not_doubleCollision hx hx2) one_le_two
  · intro h x hx
    have h2 : 2 ≤ mult I A x := (Finset.mem_filter.mp hx).2
    exact le_antisymm (h x (hsub hx)) h2

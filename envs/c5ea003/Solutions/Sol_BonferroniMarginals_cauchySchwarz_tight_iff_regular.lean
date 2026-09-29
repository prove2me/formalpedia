-- Prove2me | solution 1 for BonferroniMarginals.cauchySchwarz_tight_iff_regular
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:23:54.84437+00:00
-- url     : https://prove2.me/submissions/a33f1731-c3d4-4f0b-9af9-b609a3716c42

-- Sol generated from MachineLearning/BonferroniMarginals/Rigidity.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_Rigidity
import Theorems.Thm_BonferroniMarginals_lagrange_identity
import Theorems.Thm_BonferroniMarginals_sum_mult_eq_sum_card
import Theorems.Thm_BonferroniMarginals_sum_mult_sq_eq_sum_prod

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
theorem solution(I : Finset ι) (A : ι → Finset Ω) :
    ((∑ i ∈ I, (A i).card) ^ 2
        = (cover I A).card * ∑ p ∈ I ×ˢ I, (A p.1 ∩ A p.2).card)
      ↔ ∃ d, IsRegularCover I A d := by
  classical
  constructor
  · intro heq
    rw [← sum_mult_eq_sum_card, ← sum_mult_sq_eq_sum_prod] at heq
    have hL := lagrange_identity (cover I A) (fun x => (mult I A x : ℤ))
    have hcast : ((cover I A).card : ℤ) * (∑ x ∈ cover I A, (mult I A x : ℤ) ^ 2)
        - (∑ x ∈ cover I A, (mult I A x : ℤ)) ^ 2 = 0 := by
      have : (((∑ x ∈ cover I A, mult I A x) ^ 2 : ℕ) : ℤ)
          = (((cover I A).card * ∑ x ∈ cover I A, (mult I A x) ^ 2 : ℕ) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) heq
      push_cast at this
      linarith
    rw [hcast] at hL
    have hzero : ∑ x ∈ cover I A, ∑ y ∈ cover I A,
        ((mult I A x : ℤ) - (mult I A y : ℤ)) ^ 2 = 0 := by linarith
    have hall : ∀ x ∈ cover I A, ∀ y ∈ cover I A, mult I A x = mult I A y := by
      intro x hx y hy
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp hzero x hx
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => sq_nonneg _)).mp h1 y hy
      have : (mult I A x : ℤ) = (mult I A y : ℤ) := by nlinarith [h2]
      exact_mod_cast this
    rcases (cover I A).eq_empty_or_nonempty with hemp | ⟨x0, hx0⟩
    · exact ⟨0, fun x hx => absurd hx (by simp [hemp])⟩
    · exact ⟨mult I A x0, fun x hx => hall x hx x0 hx0⟩
  · rintro ⟨d, hd⟩
    rw [← sum_mult_eq_sum_card, ← sum_mult_sq_eq_sum_prod]
    have h1 : ∑ x ∈ cover I A, mult I A x = (cover I A).card * d := by
      rw [Finset.sum_congr rfl hd]; simp [mul_comm]
    have hsq : ∀ x ∈ cover I A, (mult I A x) ^ 2 = d ^ 2 := fun x hx => by rw [hd x hx]
    have h2 : ∑ x ∈ cover I A, (mult I A x) ^ 2 = (cover I A).card * d ^ 2 := by
      rw [Finset.sum_congr rfl hsq]; simp
    rw [h1, h2]; ring

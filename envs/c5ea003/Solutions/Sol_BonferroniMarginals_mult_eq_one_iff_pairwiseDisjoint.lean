-- Prove2me | solution 1 for BonferroniMarginals.mult_eq_one_iff_pairwiseDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:26:10.746762+00:00
-- url     : https://prove2.me/submissions/8b1a7779-94bf-40cb-b01c-1484bafbead2

-- Sol generated from MachineLearning/BonferroniMarginals/Rigidity.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_Rigidity
import Theorems.Thm_BonferroniMarginals_mem_cover

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
    (∀ x ∈ cover I A, mult I A x = 1)
      ↔ ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j) := by
  classical
  constructor
  · intro h i hi j hj hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hxc : x ∈ cover I A := mem_cover.mpr ⟨i, hi, hxi⟩
    have hsub : ({i, j} : Finset ι) ⊆ I.filter (fun k => x ∈ A k) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp [Finset.mem_filter, hi, hj, hxi, hxj]
    have hcard : 2 ≤ (I.filter (fun k => x ∈ A k)).card := by
      have := Finset.card_le_card hsub
      rwa [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton] at this
    have := h x hxc
    rw [mult] at this
    omega
  · intro h x hx
    obtain ⟨i, hi, hxi⟩ := mem_cover.mp hx
    have : I.filter (fun k => x ∈ A k) = {i} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨by simp [Finset.mem_filter, hi, hxi], ?_⟩
      intro j hj
      simp only [Finset.mem_filter] at hj
      by_contra hne
      exact (Finset.disjoint_left.mp (h j hj.1 i hi hne)) hj.2 hxi
    rw [mult, this, Finset.card_singleton]

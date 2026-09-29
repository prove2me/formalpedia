-- Prove2me | solution 1 for CyclicTypeChannel.card_symPair_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:22:52.839649+00:00
-- url     : https://prove2.me/submissions/f8e99cf2-11c1-401b-b060-facd99911bc6

-- Sol generated from Shared/CyclicTypeChannelSymmetry.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannelSymmetry
import Theorems.Thm_CyclicTypeChannel_card_swap_fiber
import Theorems.Thm_CyclicTypeChannel_symPair_eq_iff
/-
# The which-factor wall is exactly zero

A semiprime `N = p q` presents its two prime factors symmetrically: nothing in
`N mod f` can say *which* factor carries which splitting type.  Experimentally
the "which-factor" information was measured at `0.0001` bits, i.e. zero.

This file proves that it is **exactly** zero, in complete generality:  for any
sample set carrying an involution `σ` which swaps the two components of the
read-out and fixes the conditioning variable, forgetting the order of the two
components changes both the entropy and the conditional entropy by *the same*
amount, namely the probability of an off-diagonal pair.  Consequently the
mutual information of the unordered read-out equals that of the ordered one.

The entropies themselves are genuinely different (the ordered pair carries
strictly more entropy whenever off-diagonal pairs occur); it is only the
*channel* that is insensitive to the ordering.
-/

open CyclicTypeChannel

open Finset


variable {α β : Type*} [LinearOrder β]



variable [DecidableEq β] {s : Finset α} {g : α → β × β} {σ : α → α}








open CyclicTypeChannel in
theorem solution(hσs : ∀ a ∈ s, σ a ∈ s) (hσσ : ∀ a ∈ s, σ (σ a) = a)
    (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1)) (a : α) :
    (#{x ∈ s | (symPair ∘ g) x = (symPair ∘ g) a})
      = (if (g a).1 = (g a).2 then 1 else 2) * #{x ∈ s | g x = g a} := by
  classical
  have hsplit : {x ∈ s | (symPair ∘ g) x = (symPair ∘ g) a}
      = {x ∈ s | g x = g a} ∪ {x ∈ s | g x = ((g a).2, (g a).1)} := by
    ext x
    simp only [mem_filter, mem_union, Function.comp_apply]
    constructor
    · rintro ⟨hx, hsx⟩
      rcases (symPair_eq_iff _ _).1 hsx with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
      · exact ⟨hx, by rw [h]⟩
      · exact ⟨hx, (symPair_eq_iff _ _).2 (Or.inr h)⟩
  by_cases hd : (g a).1 = (g a).2
  · have heq : {x ∈ s | g x = ((g a).2, (g a).1)} = {x ∈ s | g x = g a} := by
      have : ((g a).2, (g a).1) = g a := Prod.ext_iff.2 ⟨hd.symm, hd⟩
      rw [this]
    rw [hsplit, heq, Finset.union_self, if_pos hd, one_mul]
  · have hdisj : Disjoint ({x ∈ s | g x = g a}) ({x ∈ s | g x = ((g a).2, (g a).1)}) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [mem_filter] at hx hx'
      rw [hx.2] at hx'
      exact hd (congrArg Prod.fst hx'.2)
    rw [hsplit, Finset.card_union_of_disjoint hdisj,
      card_swap_fiber hσs hσσ hgσ a, if_neg hd]
    ring

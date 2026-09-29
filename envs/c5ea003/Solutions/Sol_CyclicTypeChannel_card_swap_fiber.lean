-- Prove2me | solution 1 for CyclicTypeChannel.card_swap_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:21:13.535726+00:00
-- url     : https://prove2.me/submissions/abcb2339-e164-409e-8302-8f5befae8057

-- Sol generated from Shared/CyclicTypeChannelSymmetry.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannelSymmetry
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
omit [LinearOrder β] in
theorem solution(hσs : ∀ a ∈ s, σ a ∈ s) (hσσ : ∀ a ∈ s, σ (σ a) = a)
    (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1)) (a : α) :
    (#{x ∈ s | g x = ((g a).2, (g a).1)}) = #{x ∈ s | g x = g a} := by
  classical
  refine Finset.card_bij' (fun x _ => σ x) (fun x _ => σ x) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter] at hx ⊢
    refine ⟨hσs x hx.1, ?_⟩
    rw [hgσ x hx.1, hx.2]
  · intro x hx
    simp only [mem_filter] at hx ⊢
    refine ⟨hσs x hx.1, ?_⟩
    rw [hgσ x hx.1, hx.2]
  · intro x hx
    exact hσσ x (mem_of_mem_filter x hx)
  · intro x hx
    exact hσσ x (mem_of_mem_filter x hx)

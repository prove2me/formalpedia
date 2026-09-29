-- Prove2me | solution 1 for CyclicTypeChannel.symPair_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:59:01.397284+00:00
-- url     : https://prove2.me/submissions/a2437a7f-3450-41cf-b489-fb6eb483eba2

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



variable {s : Finset α} {g : α → β × β} {σ : α → α}








open CyclicTypeChannel in
theorem solution(z w : β × β) :
    symPair z = symPair w ↔ z = w ∨ z = (w.2, w.1) := by
  obtain ⟨z1, z2⟩ := z
  obtain ⟨w1, w2⟩ := w
  simp only [symPair, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    rcases le_total z1 z2 with hz | hz <;> rcases le_total w1 w2 with hw | hw <;>
      simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hz, hw] at h1 h2 <;>
      subst h1 <;> subst h2 <;> simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨rfl, rfl⟩
    · exact ⟨min_comm _ _, max_comm _ _⟩

-- Prove2me | solution 1 for CyclicTypeChannel.mutInfo_symPair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:27:28.810988+00:00
-- url     : https://prove2.me/submissions/b49628d1-5dd3-4375-af68-b5e90b1ce178

-- Sol generated from Shared/CyclicTypeChannelSymmetry.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelSymmetry
import Theorems.Thm_CyclicTypeChannel_condEnt_symPair
import Theorems.Thm_CyclicTypeChannel_uEnt_symPair
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
theorem solution{γ : Type*} [DecidableEq γ] {k : α → γ} (hσs : ∀ a ∈ s, σ a ∈ s)
    (hσσ : ∀ a ∈ s, σ (σ a) = a) (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1))
    (hkσ : ∀ a ∈ s, k (σ a) = k a) :
    mutInfo s (symPair ∘ g) k = mutInfo s g k := by
  rw [mutInfo, mutInfo, uEnt_symPair hσs hσσ hgσ, condEnt_symPair hσs hσσ hgσ hkσ]
  ring

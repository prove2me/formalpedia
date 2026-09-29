-- Prove2me | solution 1 for CyclicTypeChannel.condEnt_image_injOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:13:14.963649+00:00
-- url     : https://prove2.me/submissions/48413995-08f3-47a5-a241-9f018ecf3841

-- Sol generated from Shared/CyclicTypeChannelProduct.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_uEnt_image_injOn
/-
# Additivity of the counting channel over independent products

The exact values of the cyclic type-pair channel obey an unexpected law:
for coprime cyclic orders the information is *additive*,
`I_pair (m * n) = I_pair m + I_pair n`.

This file proves the structural reason.  In the counting-entropy framework of
`Shared.CyclicTypeChannel` we show that entropy, conditional entropy and mutual
information are **exactly additive over cartesian products** of the underlying
sample sets when both the read-out and the conditioning variable act
coordinatewise.  Together with the transport lemmas (invariance of the channel
under a relabelling of the sample set and under an injective recoding of the
read-out) this turns the Chinese Remainder Theorem into an additivity law for
the splitting-type channel.
-/

open CyclicTypeChannel

open Finset

variable {α α' β β' γ γ' : Type*}

/-! ## 1. Fibres of a coordinatewise read-out -/


variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*}








/-! ## 2. Transport: relabelling the sample set and recoding the read-out -/


variable [DecidableEq β] [DecidableEq γ]

















open CyclicTypeChannel in
theorem solution[DecidableEq α'] {s : Finset α} {i : α → α'} (hi : Set.InjOn i s)
    (g : α' → β) (k : α' → γ) : condEnt (s.image i) g k = condEnt s (g ∘ i) (k ∘ i) := by
  classical
  have hsub : ∀ (t : Finset α), t ⊆ s → Set.InjOn i t := by
    intro t ht
    exact hi.mono (by exact_mod_cast ht)
  rw [condEnt, condEnt, Finset.image_image, Finset.card_image_of_injOn hi]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hfib : {x ∈ s.image i | k x = c} = ({x ∈ s | (k ∘ i) x = c}).image i := by
    ext y
    simp only [mem_filter, mem_image, Function.comp_apply]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hky⟩; exact ⟨x, ⟨hx, hky⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hkx⟩, rfl⟩; exact ⟨⟨x, hx, rfl⟩, hkx⟩
  rw [hfib, Finset.card_image_of_injOn (hsub _ (filter_subset _ _)),
    uEnt_image_injOn (hsub _ (filter_subset _ _))]

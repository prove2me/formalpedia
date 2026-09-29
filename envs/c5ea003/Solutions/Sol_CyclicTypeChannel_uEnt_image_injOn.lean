-- Prove2me | solution 1 for CyclicTypeChannel.uEnt_image_injOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:12:06.301278+00:00
-- url     : https://prove2.me/submissions/57f51591-d4e1-4fac-a751-d137f8047af0

-- Sol generated from Shared/CyclicTypeChannelProduct.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
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
    (g : α' → β) : uEnt (s.image i) g = uEnt s (g ∘ i) := by
  classical
  have hsub : ∀ (t : Finset α), t ⊆ s → Set.InjOn i t := by
    intro t ht
    exact hi.mono (by exact_mod_cast ht)
  have hfib : ∀ a ∈ s, {x ∈ s.image i | g x = g (i a)}
      = ({x ∈ s | (g ∘ i) x = (g ∘ i) a}).image i := by
    intro a _
    ext y
    simp only [mem_filter, mem_image, Function.comp_apply]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hgy⟩; exact ⟨x, ⟨hx, hgy⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hgx⟩, rfl⟩; exact ⟨⟨x, hx, rfl⟩, hgx⟩
  rw [uEnt, uEnt, Finset.card_image_of_injOn hi]
  congr 1
  congr 1
  rw [Finset.sum_image (fun x hx y hy hxy => hi hx hy hxy)]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hfib a ha, Finset.card_image_of_injOn (hsub _ (filter_subset _ _))]

-- Prove2me | solution 1 for CyclicTypeChannel.uEnt_comp_injOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:08:47.342841+00:00
-- url     : https://prove2.me/submissions/cc349156-ecf4-4090-bd20-344b1f25e70a

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
theorem solution[DecidableEq β'] {s : Finset α} {g : α → β} {f : β → β'}
    (hf : Set.InjOn f (g '' s)) : uEnt s (f ∘ g) = uEnt s g := by
  classical
  have hfib : ∀ a ∈ s, {x ∈ s | (f ∘ g) x = (f ∘ g) a} = {x ∈ s | g x = g a} := by
    intro a ha
    ext x
    simp only [mem_filter, Function.comp_apply]
    constructor
    · rintro ⟨hx, hfx⟩
      exact ⟨hx, hf ⟨x, hx, rfl⟩ ⟨a, ha, rfl⟩ hfx⟩
    · rintro ⟨hx, hgx⟩
      exact ⟨hx, by rw [hgx]⟩
  rw [uEnt, uEnt]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun a ha => by rw [hfib a ha]

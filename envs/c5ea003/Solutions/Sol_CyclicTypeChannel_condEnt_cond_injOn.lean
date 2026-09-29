-- Prove2me | solution 1 for CyclicTypeChannel.condEnt_cond_injOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:10:08.054863+00:00
-- url     : https://prove2.me/submissions/bd3ed24a-ec52-4fff-b983-20fa2f006072

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
theorem solution[DecidableEq γ'] {s : Finset α} {g : α → β} {k : α → γ} {f : γ → γ'}
    (hf : Set.InjOn f (k '' s)) : condEnt s g (f ∘ k) = condEnt s g k := by
  classical
  rw [condEnt, condEnt, ← Finset.image_image]
  rw [Finset.sum_image (by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hy
    exact hf ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hxy)]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
  have hfib : {x ∈ s | (f ∘ k) x = f (k a)} = {x ∈ s | k x = k a} := by
    ext x
    simp only [mem_filter, Function.comp_apply]
    exact ⟨fun h => ⟨h.1, hf ⟨x, h.1, rfl⟩ ⟨a, ha, rfl⟩ h.2⟩, fun h => ⟨h.1, by rw [h.2]⟩⟩
  rw [hfib]

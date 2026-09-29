-- Prove2me | solution 1 for CyclicTypeChannel.uEnt_map
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:20:23.864864+00:00
-- url     : https://prove2.me/submissions/bb5de353-f663-47c3-8d72-a015d3565aff

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
theorem solution{s : Finset α} (e : α ↪ α') (g : α' → β) :
    uEnt (s.map e) g = uEnt s (g ∘ e) := by
  classical
  have hfib : ∀ a ∈ s, (#{x ∈ s.map e | g x = g (e a)}) = #{x ∈ s | (g ∘ e) x = (g ∘ e) a} := by
    intro a _
    rw [Finset.filter_map]
    exact Finset.card_map _
  rw [uEnt, uEnt, Finset.card_map]
  congr 1
  congr 1
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun a ha => ?_
  have h := hfib a ha
  simp only [Function.comp_apply] at h ⊢
  rw [h]

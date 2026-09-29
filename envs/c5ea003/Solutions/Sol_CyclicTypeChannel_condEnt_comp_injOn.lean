-- Prove2me | solution 1 for CyclicTypeChannel.condEnt_comp_injOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:10:06.979047+00:00
-- url     : https://prove2.me/submissions/64eb7c9e-a209-4812-acc2-0ac2293be4d1

-- Sol generated from Shared/CyclicTypeChannelProduct.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_uEnt_comp_injOn
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
theorem solution[DecidableEq β'] {s : Finset α} {g : α → β} {k : α → γ} {f : β → β'}
    (hf : Set.InjOn f (g '' s)) : condEnt s (f ∘ g) k = condEnt s g k := by
  classical
  refine Finset.sum_congr rfl fun c _ => ?_
  have hsub : ({x ∈ s | k x = c} : Finset α) ⊆ s := filter_subset _ _
  have : Set.InjOn f (g '' ({x ∈ s | k x = c} : Finset α)) := by
    refine hf.mono ?_
    exact Set.image_mono (by exact_mod_cast hsub)
  rw [uEnt_comp_injOn this]

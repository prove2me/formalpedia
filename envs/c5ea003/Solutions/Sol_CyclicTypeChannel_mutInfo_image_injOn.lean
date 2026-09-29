-- Prove2me | solution 1 for CyclicTypeChannel.mutInfo_image_injOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:14:54.170222+00:00
-- url     : https://prove2.me/submissions/48f527a2-594f-4cfa-96eb-86c79e19dbf7

-- Sol generated from Shared/CyclicTypeChannelProduct.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_condEnt_image_injOn
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
    (g : α' → β) (k : α' → γ) : mutInfo (s.image i) g k = mutInfo s (g ∘ i) (k ∘ i) := by
  rw [mutInfo, mutInfo, uEnt_image_injOn hi, condEnt_image_injOn hi]

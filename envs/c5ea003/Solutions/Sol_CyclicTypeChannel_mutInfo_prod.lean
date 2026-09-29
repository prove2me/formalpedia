-- Prove2me | solution 1 for CyclicTypeChannel.mutInfo_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:19:28.090837+00:00
-- url     : https://prove2.me/submissions/073f0f7d-5bef-4b12-b993-98f5a9f8456e

-- Sol generated from Shared/CyclicTypeChannelProduct.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_condEnt_prod
import Theorems.Thm_CyclicTypeChannel_uEnt_prod
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
theorem solution[DecidableEq β₁] [DecidableEq β₂] [DecidableEq γ₁] [DecidableEq γ₂]
    {s₁ : Finset α₁} {s₂ : Finset α₂} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
    (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) (k₁ : α₁ → γ₁) (k₂ : α₂ → γ₂) :
    mutInfo (s₁ ×ˢ s₂) (fun x => (g₁ x.1, g₂ x.2)) (fun x => (k₁ x.1, k₂ x.2))
      = mutInfo s₁ g₁ k₁ + mutInfo s₂ g₂ k₂ := by
  rw [mutInfo, mutInfo, mutInfo, uEnt_prod h₁ h₂, condEnt_prod h₁ h₂]
  ring

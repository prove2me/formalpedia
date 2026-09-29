-- Prove2me | Theorems.Thm_CyclicTypeChannel_mutInfo_prod
-- name    : CyclicTypeChannel.mutInfo_prod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:27:23.253668+00:00
-- url     : https://prove2.me/theorems/926d3e80-087a-4628-8002-c4caf849be60
-- title:
--   Additivity of the channel over independent products.
-- statement:
--   **Additivity of the channel over independent products.**  If the read-out
--   and the conditioning variable both act coordinatewise on a product sample set,
--   the mutual information is the sum of the two component informations.
--
--   ```lean
--   theorem CyclicTypeChannel.mutInfo_prod[DecidableEq β₁] [DecidableEq β₂] [DecidableEq γ₁] [DecidableEq γ₂]
--       {s₁ : Finset α₁} {s₂ : Finset α₂} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
--       (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) (k₁ : α₁ → γ₁) (k₂ : α₂ → γ₂) :
--       mutInfo (s₁ ×ˢ s₂) (fun x => (g₁ x.1, g₂ x.2)) (fun x => (k₁ x.1, k₂ x.2))
--         = mutInfo s₁ g₁ k₁ + mutInfo s₂ g₂ k₂ := by sorry
--
--   /-! ## 2. Transport: relabelling the sample set and recoding the read-out -/
--
--
--   variable [DecidableEq β] [DecidableEq γ]
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelProduct.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelProduct.lean#L154

-- Thm stub generated from Shared/CyclicTypeChannelProduct.lean
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

theorem CyclicTypeChannel.mutInfo_prod[DecidableEq β₁] [DecidableEq β₂] [DecidableEq γ₁] [DecidableEq γ₂]
    {s₁ : Finset α₁} {s₂ : Finset α₂} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
    (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) (k₁ : α₁ → γ₁) (k₂ : α₂ → γ₂) :
    mutInfo (s₁ ×ˢ s₂) (fun x => (g₁ x.1, g₂ x.2)) (fun x => (k₁ x.1, k₂ x.2))
      = mutInfo s₁ g₁ k₁ + mutInfo s₂ g₂ k₂ := by sorry

-- Prove2me | Theorems.Thm_CyclicTypeChannel_condEnt_prod
-- name    : CyclicTypeChannel.condEnt_prod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:26:51.825429+00:00
-- url     : https://prove2.me/theorems/000fc1db-6d51-44b3-98c2-fde3c369dbc9
-- title:
--   Additivity of conditional entropy over independent products.
-- statement:
--   **Additivity of conditional entropy over independent products.**
--
--   ```lean
--   theorem CyclicTypeChannel.condEnt_prod[DecidableEq β₁] [DecidableEq β₂] [DecidableEq γ₁] [DecidableEq γ₂]
--       {s₁ : Finset α₁} {s₂ : Finset α₂} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
--       (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) (k₁ : α₁ → γ₁) (k₂ : α₂ → γ₂) :
--       condEnt (s₁ ×ˢ s₂) (fun x => (g₁ x.1, g₂ x.2)) (fun x => (k₁ x.1, k₂ x.2))
--         = condEnt s₁ g₁ k₁ + condEnt s₂ g₂ k₂ := by sorry
--
--
--   /-! ## 2. Transport: relabelling the sample set and recoding the read-out -/
--
--
--   variable [DecidableEq β] [DecidableEq γ]
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelProduct.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelProduct.lean#L98

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

theorem CyclicTypeChannel.condEnt_prod[DecidableEq β₁] [DecidableEq β₂] [DecidableEq γ₁] [DecidableEq γ₂]
    {s₁ : Finset α₁} {s₂ : Finset α₂} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
    (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) (k₁ : α₁ → γ₁) (k₂ : α₂ → γ₂) :
    condEnt (s₁ ×ˢ s₂) (fun x => (g₁ x.1, g₂ x.2)) (fun x => (k₁ x.1, k₂ x.2))
      = condEnt s₁ g₁ k₁ + condEnt s₂ g₂ k₂ := by sorry

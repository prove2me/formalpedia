-- Prove2me | Theorems.Thm_CyclicTypeChannel_uEnt_prod
-- name    : CyclicTypeChannel.uEnt_prod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:27:04.449984+00:00
-- url     : https://prove2.me/theorems/0557fffe-3b6a-4b64-a340-64afb726b378
-- title:
--   Additivity of entropy over independent products.
-- statement:
--   **Additivity of entropy over independent products.**
--
--   ```lean
--   theorem CyclicTypeChannel.uEnt_prod[DecidableEq β₁] [DecidableEq β₂] {s₁ : Finset α₁} {s₂ : Finset α₂}
--       (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) :
--       uEnt (s₁ ×ˢ s₂) (fun x => (g₁ x.1, g₂ x.2)) = uEnt s₁ g₁ + uEnt s₂ g₂ := by sorry
--
--
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
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelProduct.lean#L46

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

theorem CyclicTypeChannel.uEnt_prod[DecidableEq β₁] [DecidableEq β₂] {s₁ : Finset α₁} {s₂ : Finset α₂}
    (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) :
    uEnt (s₁ ×ˢ s₂) (fun x => (g₁ x.1, g₂ x.2)) = uEnt s₁ g₁ + uEnt s₂ g₂ := by sorry

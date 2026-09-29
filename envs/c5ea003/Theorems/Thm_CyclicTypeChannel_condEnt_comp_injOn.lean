-- Prove2me | Theorems.Thm_CyclicTypeChannel_condEnt_comp_injOn
-- name    : CyclicTypeChannel.condEnt_comp_injOn
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:26:27.807464+00:00
-- url     : https://prove2.me/theorems/0041c02d-8285-46a4-afc3-69b9ccd68bfb
-- title:
--   Conditional entropy is unchanged by an injective recoding of the read-out.
-- statement:
--   Conditional entropy is unchanged by an injective recoding of the read-out.
--
--   ```lean
--   theorem CyclicTypeChannel.condEnt_comp_injOn[DecidableEq β'] {s : Finset α} {g : α → β} {k : α → γ} {f : β → β'}
--       (hf : Set.InjOn f (g '' s)) : condEnt s (f ∘ g) k = condEnt s g k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelProduct.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelProduct.lean#L233

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








/-! ## 2. Transport: relabelling the sample set and recoding the read-out -/


variable [DecidableEq β] [DecidableEq γ]

theorem CyclicTypeChannel.condEnt_comp_injOn[DecidableEq β'] {s : Finset α} {g : α → β} {k : α → γ} {f : β → β'}
    (hf : Set.InjOn f (g '' s)) : condEnt s (f ∘ g) k = condEnt s g k := by sorry

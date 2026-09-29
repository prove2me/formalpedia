-- Prove2me | Theorems.Thm_CyclicTypeChannel_uEnt_congr
-- name    : CyclicTypeChannel.uEnt_congr
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:26:39.49175+00:00
-- url     : https://prove2.me/theorems/77541dbf-713c-4bbf-869b-b57cdd29cd3a
-- title:
--   Entropy only depends on the values the read-out takes on the sample set.
-- statement:
--   Entropy only depends on the values the read-out takes on the sample set.
--
--   ```lean
--   theorem CyclicTypeChannel.uEnt_congr{s : Finset α} {g g' : α → β} (h : ∀ a ∈ s, g a = g' a) :
--       uEnt s g = uEnt s g' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelProduct.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelProduct.lean#L173

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

theorem CyclicTypeChannel.uEnt_congr{s : Finset α} {g g' : α → β} (h : ∀ a ∈ s, g a = g' a) :
    uEnt s g = uEnt s g' := by sorry

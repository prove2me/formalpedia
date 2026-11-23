-- Prove2me | Theorems.Thm_agreement_implies_component_agreement
-- name    : agreement_implies_component_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:32:20.572808+00:00
-- url     : https://prove2.me/theorems/982eb64c-b5b8-4499-9da9-14f5d5023a45
-- title:
--   agreement implies component agreement: agreement implies component agreement
-- statement:
--   The agreement implies component agreement construction uses the agreement implies component agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L373-L382
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L373-L382

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem agreement_implies_component_agreement {F : Type*} [Field F] [DecidableEq F]
  (D : Finset F) (m : ℕ) (f g : F → F) (S : Finset F) (_hS : S ⊆ D)
  (h_blocks : ∀ z ∈ pow_domain S m, Block D m z ⊆ S) :
  (∀ x ∈ S, f x = g x) →
  ∀ i : Fin m, ∀ z ∈ pow_domain S m,
    folding_component D m f i z = folding_component D m g i z := by sorry

-- Prove2me | Theorems.Thm_card_block_le_m
-- name    : card_block_le_m
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:54:06.435232+00:00
-- url     : https://prove2.me/theorems/d0f2616d-f660-4ae8-bffb-94dde568f390
-- title:
--   card block le m: card block le m
-- statement:
--   The card block le m construction uses the card block le m property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L915-L925
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L915-L925

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem card_block_le_m {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ) (z : F)
    (hm : m > 0) : (Block D m z).card ≤ m := by sorry

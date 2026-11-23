-- Prove2me | Theorems.Thm_foldable_pow_domain_card
-- name    : foldable_pow_domain_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:54:05.639911+00:00
-- url     : https://prove2.me/theorems/5a0d8ea1-01ae-42f5-8fc9-65839d396cc5
-- title:
--   foldable pow domain card: foldable pow domain card
-- statement:
--   The foldable pow domain card construction uses the foldable pow domain card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L279-L298
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L279-L298

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem foldable_pow_domain_card {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (h_foldable : IsFoldable D m) :
    D.card = m * (pow_domain D m).card := by sorry

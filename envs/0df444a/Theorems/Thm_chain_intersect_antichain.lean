-- Prove2me | Theorems.Thm_chain_intersect_antichain
-- name    : chain_intersect_antichain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:08:36.454263+00:00
-- url     : https://prove2.me/theorems/401b6ef7-840b-4e9a-a796-d81a2faf86f1
-- title:
--   chain intersect antichain: chain intersect antichain
-- statement:
--   The chain intersect antichain construction uses the chain intersect antichain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/ForMathlib/Misc.lean#L17-L25
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/ForMathlib/Misc.lean#L17-L25

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.WellFoundedSet
import Definitions.Def_AharoniKorman_ForMathlib_Misc
set_option autoImplicit true

theorem chain_intersect_antichain {α : Type*} [PartialOrder α] {s t : Set α}
    (hs : IsChain (· ≤ ·) s) (ht : IsAntichain (· ≤ ·) t) :
    (s ∩ t).Subsingleton := by sorry

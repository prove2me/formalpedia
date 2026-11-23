-- Prove2me | Theorems.Thm_one_le_apply_of_q_reduced_of_rank_geq_one
-- name    : one_le_apply_of_q_reduced_of_rank_geq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:49:11.477039+00:00
-- url     : https://prove2.me/theorems/76a5ecde-a0a0-466d-b913-f4c5676aec1d
-- title:
--   one le apply of q reduced of rank geq one: one le apply of q reduced of rank geq one
-- statement:
--   The one le apply of q reduced of rank geq one construction uses the one le apply of q reduced of rank geq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L332-L352
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L332-L352

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem one_le_apply_of_q_reduced_of_rank_geq_one {G : CFGraph} {q : G.V}
    {D : CFDiv G} (hred : q_reduced G q D) (hrank : rank G D ≥ 1) :
    1 ≤ D q := by sorry

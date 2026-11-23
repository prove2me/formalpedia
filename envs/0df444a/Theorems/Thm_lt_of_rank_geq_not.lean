-- Prove2me | Theorems.Thm_lt_of_rank_geq_not
-- name    : lt_of_rank_geq_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:47:24.965094+00:00
-- url     : https://prove2.me/theorems/b3e45e89-2fe1-4d72-a415-ddef8d39b8e3
-- title:
--   lt of rank geq not: lt of rank geq not
-- statement:
--   If $r(D) \ge r_1$ holds but $r(D) \ge r_2$ does not, then $r_1 < r_2$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L165-L169
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L165-L169

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem lt_of_rank_geq_not (G : CFGraph) (D : CFDiv G) (r1 r2 : ℤ) :
  rank_geq G D r1 → ¬(rank_geq G D r2) → r1 < r2 := by sorry

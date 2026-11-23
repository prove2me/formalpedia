-- Prove2me | Theorems.Thm_rank_get_effective
-- name    : rank_get_effective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:47:29.290072+00:00
-- url     : https://prove2.me/theorems/519a0949-0062-409b-9785-ae6a15679896
-- title:
--   rank get effective: rank get effective
-- statement:
--   There is an effective divisor $E$ of degree $r(D)+1$ such that $D-E$ is not winnable.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L288-L294
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L288-L294

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem rank_get_effective (G : CFGraph) (D : CFDiv G) :
  ∃ E : CFDiv G, effective E ∧ deg E = rank G D + 1 ∧ ¬(winnable G (D-E)) := by sorry

-- Prove2me | Theorems.Thm_maximal_unwinnable_preserved
-- name    : maximal_unwinnable_preserved
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:47:25.86949+00:00
-- url     : https://prove2.me/theorems/d74bae6d-599d-461d-862f-cde0864ef585
-- title:
--   maximal unwinnable preserved: maximal unwinnable preserved
-- statement:
--   Being maximal unwinnable is preserved under linear equivalence.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L45-L54
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean#L45-L54

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem maximal_unwinnable_preserved (G : CFGraph) (D1 D2 : CFDiv G) :
  maximal_unwinnable G D1 → linear_equiv G D1 D2 → maximal_unwinnable G D2 := by sorry

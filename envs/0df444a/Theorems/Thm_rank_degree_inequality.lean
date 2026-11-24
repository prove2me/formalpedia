-- Prove2me | Theorems.Thm_rank_degree_inequality
-- name    : rank_degree_inequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:04.063327+00:00
-- url     : https://prove2.me/theorems/c3a51da6-f511-4cb8-b5cc-6cae0a0008ff
-- title:
--   rank degree inequality: rank degree inequality
-- statement:
--   The strict Riemann-Roch inequality: $\deg(D) - g < r(D) - r(K_G - D)$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L507-L544
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L507-L544

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem rank_degree_inequality
    {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
    deg D - genus G < rank G D - rank G (canonical_divisor G - D) := by sorry

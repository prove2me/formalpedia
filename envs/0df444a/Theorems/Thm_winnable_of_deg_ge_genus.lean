-- Prove2me | Theorems.Thm_winnable_of_deg_ge_genus
-- name    : winnable_of_deg_ge_genus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:51:50.838355+00:00
-- url     : https://prove2.me/theorems/e6944cfb-284f-4b38-9c70-e11220837aa3
-- title:
--   winnable of deg ge genus: winnable of deg ge genus
-- statement:
--   A divisor of degree at least $g$ is winnable.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L214-L225
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L214-L225

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem winnable_of_deg_ge_genus {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) : deg D ≥ genus G → winnable G D := by sorry

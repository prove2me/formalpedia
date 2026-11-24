-- Prove2me | Theorems.Thm_gonality_leq_genus_add_one
-- name    : gonality_leq_genus_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:04.760732+00:00
-- url     : https://prove2.me/theorems/f44af2e6-e9ea-472f-bc5e-c6b8c60bd798
-- title:
--   gonality leq genus add one: gonality leq genus add one
-- statement:
--   A connected graph has gonality at most $g+1$, where $g$ is its genus.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean#L243-L260
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean#L243-L260

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
universe u
open Multiset Finset

theorem gonality_leq_genus_add_one
    {G : CFGraph} (h_conn : graph_connected G) : gonality_leq G (genus G + 1) := by sorry

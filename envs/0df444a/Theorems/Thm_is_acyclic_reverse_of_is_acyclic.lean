-- Prove2me | Theorems.Thm_is_acyclic_reverse_of_is_acyclic
-- name    : is_acyclic_reverse_of_is_acyclic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:50:08.510375+00:00
-- url     : https://prove2.me/theorems/f66b8fd9-176a-4a6f-a1b5-b503f6aff9c5
-- title:
--   is acyclic reverse of is acyclic: is acyclic reverse of is acyclic
-- statement:
--   The reverse of an acyclic orientation is also acyclic.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L918-L940
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L918-L940

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem is_acyclic_reverse_of_is_acyclic (G : CFGraph) (O : CFOrientation G)
    (h_acyclic : is_acyclic G O) :
  is_acyclic G (O.reverse G) := by sorry

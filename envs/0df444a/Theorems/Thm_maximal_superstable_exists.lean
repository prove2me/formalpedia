-- Prove2me | Theorems.Thm_maximal_superstable_exists
-- name    : maximal_superstable_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:50:06.665017+00:00
-- url     : https://prove2.me/theorems/72a84fbc-9a18-4ed7-bdb2-5e2a9c7d2aee
-- title:
--   maximal superstable exists: maximal superstable exists
-- statement:
--   Every superstable configuration extends to a maximal superstable configuration.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L1170-L1178
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L1170-L1178

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem maximal_superstable_exists (G : CFGraph) (q : G.V) (c : Config G q)
    (h_super : superstable G q c) :
    ∃ c' : Config G q, maximal_superstable G c' ∧ c ≤ c' := by sorry

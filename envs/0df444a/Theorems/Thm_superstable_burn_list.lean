-- Prove2me | Theorems.Thm_superstable_burn_list
-- name    : superstable_burn_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:47:01.473378+00:00
-- url     : https://prove2.me/theorems/c66c4b89-98f4-460f-92ab-32cff6706331
-- title:
--   superstable burn list: superstable burn list
-- statement:
--   A superstable configuration admits a complete burn list containing every vertex of $G$.
--   This is the key output of Dhar's burning algorithm: in a superstable configuration, the
--   whole graph burns.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L566-L588
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L566-L588

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem superstable_burn_list (G : CFGraph) {q : G.V} (c : Config G q) (h_ss : superstable G q c) : ∃ L : burn_list G c, ∀ v : G.V, v ∈ L.list := by sorry

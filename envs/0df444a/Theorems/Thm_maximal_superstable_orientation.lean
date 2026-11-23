-- Prove2me | Theorems.Thm_maximal_superstable_orientation
-- name    : maximal_superstable_orientation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:49:58.106671+00:00
-- url     : https://prove2.me/theorems/0a906d00-2c8d-42d9-898a-1ed68e9c75af
-- title:
--   maximal superstable orientation: maximal superstable orientation
-- statement:
--   Every maximal superstable configuration comes from an acyclic orientation.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 4.8,
--   part 2 (surjectivity).
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L1184-L1192
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L1184-L1192

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem maximal_superstable_orientation (G : CFGraph) (q : G.V) (c : Config G q)
    (h_max : maximal_superstable G c) :
    ∃ (O : CFOrientation G) (hO : acyclic_with_unique_source G O q),
      orientation_to_config G O q hO = c := by sorry

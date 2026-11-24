-- Prove2me | Theorems.Thm_orientation_determined_by_indegrees
-- name    : orientation_determined_by_indegrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:50:08.384322+00:00
-- url     : https://prove2.me/theorems/2dd38b8e-2d8b-4110-b772-bbfd5f2c5aaa
-- title:
--   orientation determined by indegrees: orientation determined by indegrees
-- statement:
--   An acyclic orientation is uniquely determined by its in-degree sequence.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Lemma 4.3.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L478-L578
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L478-L578

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem orientation_determined_by_indegrees {G : CFGraph}
  (O O' : CFOrientation G) :
  is_acyclic G O → is_acyclic G O' →
  (∀ v : G.V, indeg G O v = indeg G O' v) →
  O = O' := by sorry

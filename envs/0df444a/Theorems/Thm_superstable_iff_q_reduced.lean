-- Prove2me | Theorems.Thm_superstable_iff_q_reduced
-- name    : superstable_iff_q_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:45:15.122806+00:00
-- url     : https://prove2.me/theorems/be8f0367-eb1e-4742-9cc5-706634b4a001
-- title:
--   superstable iff q reduced: superstable iff q reduced
-- statement:
--   A configuration $c$ is superstable if and only if `toDiv d c` is $q$-reduced,
--   for any prescribed degree $d$.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Remark 3.14.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L310-L348
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L310-L348

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem superstable_iff_q_reduced (G : CFGraph) (q : G.V) (d : ℤ) (c : Config G q) :
  superstable G q c ↔ q_reduced G q (toDiv d c) := by sorry

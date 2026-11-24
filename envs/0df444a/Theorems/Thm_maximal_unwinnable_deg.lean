-- Prove2me | Theorems.Thm_maximal_unwinnable_deg
-- name    : maximal_unwinnable_deg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:52:01.406307+00:00
-- url     : https://prove2.me/theorems/1fd07466-a2d7-4247-be2c-2af4c965cda5
-- title:
--   maximal unwinnable deg: maximal unwinnable deg
-- statement:
--   A maximal unwinnable divisor has degree $g - 1$, computed from its canonical
--   $q$-reduced representative and canonical configuration.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 4.9(4).
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L343-L363
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L343-L363

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem maximal_unwinnable_deg
  {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
  maximal_unwinnable G D → deg D = genus G - 1 := by sorry

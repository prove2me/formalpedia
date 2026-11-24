-- Prove2me | Theorems.Thm_maximal_unwinnable_char
-- name    : maximal_unwinnable_char
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:52:40.056634+00:00
-- url     : https://prove2.me/theorems/fe7e61e1-f8bb-4c00-85c6-3fed55047adf
-- title:
--   maximal unwinnable char: maximal unwinnable char
-- statement:
--   A divisor $D$ is maximal unwinnable if and only if its canonical $q$-reduced
--   representative has the form $c-q$, with $c$ the associated maximal superstable
--   configuration.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 4.9(2),
--   in canonical form.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L321-L337
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean#L321-L337

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem maximal_unwinnable_char {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  maximal_unwinnable G D ↔
    maximal_superstable G (qReducedConfig h_conn q D) ∧
    qReducedRep h_conn q D =
      (qReducedConfig h_conn q D).chips - one_chip q := by sorry

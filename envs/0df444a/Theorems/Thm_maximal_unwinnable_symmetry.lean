-- Prove2me | Theorems.Thm_maximal_unwinnable_symmetry
-- name    : maximal_unwinnable_symmetry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:50.351813+00:00
-- url     : https://prove2.me/theorems/b735ef62-9ec9-4de6-9f61-b054e9da368d
-- title:
--   maximal unwinnable symmetry: maximal unwinnable symmetry
-- statement:
--   $D$ is maximal unwinnable if and only if $K_G - D$ is maximal unwinnable.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 5.11.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean#L38-L91
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean#L38-L91

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
universe u
open Multiset Finset

theorem maximal_unwinnable_symmetry
    {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
  maximal_unwinnable G D ↔ maximal_unwinnable G (canonical_divisor G - D) := by sorry

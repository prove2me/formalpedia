-- Prove2me | Theorems.Thm_ordiv_unwinnable
-- name    : ordiv_unwinnable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:50:14.22924+00:00
-- url     : https://prove2.me/theorems/a4e6324a-1967-417f-ba6b-bb7a4d726402
-- title:
--   ordiv unwinnable: ordiv unwinnable
-- statement:
--   The orientation divisor $D(\mathcal{O})$ of an acyclic orientation $\mathcal{O}$ is not
--   winnable.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Proposition 4.11.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L669-L781
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L669-L781

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem ordiv_unwinnable (G : CFGraph) (O : CFOrientation G) :
  is_acyclic G O → ¬ winnable G (ordiv G O) := by sorry

-- Prove2me | Theorems.Thm_degree_of_canonical_divisor
-- name    : degree_of_canonical_divisor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:50:06.222404+00:00
-- url     : https://prove2.me/theorems/0e0d4da7-31c5-41c4-b399-671777e2d9d4
-- title:
--   degree of canonical divisor: degree of canonical divisor
-- statement:
--   The degree of the canonical divisor is $2g - 2$, where $g$ is the genus of $G$.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Exercise 5.8.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L968-L988
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L968-L988

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem degree_of_canonical_divisor (G : CFGraph) :
    deg (canonical_divisor G) = 2 * genus G - 2 := by sorry

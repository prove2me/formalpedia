-- Prove2me | Theorems.Thm_linear_equiv_preserves_deg
-- name    : linear_equiv_preserves_deg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:42:01.319199+00:00
-- url     : https://prove2.me/theorems/429e63e5-2bdb-4cd9-8b7d-3359dfea538d
-- title:
--   linear equiv preserves deg: linear equiv preserves deg
-- statement:
--   Linearly equivalent divisors have the same degree.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Proposition 1.15.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L514-L519
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L514-L519

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty

theorem linear_equiv_preserves_deg (G : CFGraph) (D D' : CFDiv G) (h_equiv : linear_equiv G D D') :
  deg D = deg D' := by sorry

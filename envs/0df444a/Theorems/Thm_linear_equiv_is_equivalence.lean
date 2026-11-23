-- Prove2me | Theorems.Thm_linear_equiv_is_equivalence
-- name    : linear_equiv_is_equivalence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:44:17.381598+00:00
-- url     : https://prove2.me/theorems/32f9afec-f3c3-40f2-931a-7b48e6fdb9ac
-- title:
--   linear equiv is equivalence: linear equiv is equivalence
-- statement:
--   Linear equivalence is an equivalence relation on $\operatorname{Div}(G)$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L241-L242
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L241-L242

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

theorem linear_equiv_is_equivalence (G : CFGraph) : Equivalence (linear_equiv G) := by sorry

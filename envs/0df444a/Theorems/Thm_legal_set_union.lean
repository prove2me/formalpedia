-- Prove2me | Theorems.Thm_legal_set_union
-- name    : legal_set_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:44:56.767092+00:00
-- url     : https://prove2.me/theorems/a197da67-a330-440c-b87c-68bc197a5df2
-- title:
--   legal set union: legal set union
-- statement:
--   The legal set union construction uses the legal set union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1048-L1054
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1048-L1054

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
open Matrix

theorem legal_set_union (G : CFGraph) {D : CFDiv G} {S T : Finset G.V}
    (hS : legal_set G D S) (hT : legal_set G D T) :
    legal_set G D (S ∪ T) := by sorry

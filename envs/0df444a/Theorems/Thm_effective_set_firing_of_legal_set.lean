-- Prove2me | Theorems.Thm_effective_set_firing_of_legal_set
-- name    : effective_set_firing_of_legal_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:44:45.603049+00:00
-- url     : https://prove2.me/theorems/8e3ee194-d945-417e-9871-b7faaf97f98d
-- title:
--   effective set firing of legal set: effective set firing of legal set
-- statement:
--   The effective set firing of legal set construction uses the effective set firing of legal set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1028-L1036
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1028-L1036

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

theorem effective_set_firing_of_legal_set (G : CFGraph) {D : CFDiv G}
    {S : Finset G.V} (hD : effective D) (hS : legal_set G D S) :
    effective (set_firing G D S) := by sorry

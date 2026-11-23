-- Prove2me | Theorems.Thm_q_effective_set_firing_of_legal_set
-- name    : q_effective_set_firing_of_legal_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:43:41.5104+00:00
-- url     : https://prove2.me/theorems/671c59b4-584c-47e4-b0ea-a82128012940
-- title:
--   q effective set firing of legal set: q effective set firing of legal set
-- statement:
--   Firing a legal set preserves effectivity away from a distinguished vertex.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1039-L1046
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1039-L1046

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

theorem q_effective_set_firing_of_legal_set (G : CFGraph) {q : G.V} {D : CFDiv G}
    {S : Finset G.V} (hD : q_effective q D) (hS : legal_set G D S) :
    q_effective q (set_firing G D S) := by sorry

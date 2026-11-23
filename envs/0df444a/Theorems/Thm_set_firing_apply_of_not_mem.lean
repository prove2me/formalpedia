-- Prove2me | Theorems.Thm_set_firing_apply_of_not_mem
-- name    : set_firing_apply_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:43:09.096682+00:00
-- url     : https://prove2.me/theorems/fcd6de48-2a6f-4e59-945a-241a6d2cc837
-- title:
--   set firing apply of not mem: set firing apply of not mem
-- statement:
--   The set firing apply of not mem construction uses the set firing apply of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L172-L175
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L172-L175

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

theorem set_firing_apply_of_not_mem (G : CFGraph) (D : CFDiv G)
    {S : Finset G.V} {v : G.V} (hv : v ∉ S) :
    set_firing G D S v = D v + outdeg_S G Sᶜ v := by sorry

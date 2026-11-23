-- Prove2me | Theorems.Thm_set_firing_apply_of_mem
-- name    : set_firing_apply_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:42:08.022895+00:00
-- url     : https://prove2.me/theorems/151af233-45ed-4fa1-b95b-0ff0ef6bab2c
-- title:
--   set firing apply of mem: set firing apply of mem
-- statement:
--   The set firing apply of mem construction uses the set firing apply of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L167-L170
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L167-L170

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

theorem set_firing_apply_of_mem (G : CFGraph) (D : CFDiv G) {S : Finset G.V}
    {v : G.V} (hv : v ∈ S) :
    set_firing G D S v = D v - outdeg_S G S v := by sorry

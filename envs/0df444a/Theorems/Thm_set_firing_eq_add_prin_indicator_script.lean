-- Prove2me | Theorems.Thm_set_firing_eq_add_prin_indicator_script
-- name    : set_firing_eq_add_prin_indicator_script
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:43:13.581925+00:00
-- url     : https://prove2.me/theorems/cc0439f1-f8e3-4afc-8f04-c27f1c43e118
-- title:
--   set firing eq add prin indicator script: set firing eq add prin indicator script
-- statement:
--   Firing a set once is the same as adding the principal divisor of its indicator script.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L298-L312
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L298-L312

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

theorem set_firing_eq_add_prin_indicator_script (G : CFGraph) (D : CFDiv G)
    (S : Finset G.V) :
    set_firing G D S = D + prin G (indicator_script G S) := by sorry

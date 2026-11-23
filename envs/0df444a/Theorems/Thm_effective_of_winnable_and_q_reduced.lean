-- Prove2me | Theorems.Thm_effective_of_winnable_and_q_reduced
-- name    : effective_of_winnable_and_q_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:42:08.688831+00:00
-- url     : https://prove2.me/theorems/8d96968a-8c81-4fac-9d97-e82603a153ef
-- title:
--   effective of winnable and q reduced: effective of winnable and q reduced
-- statement:
--   A winnable $q$-reduced divisor is effective.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1236-L1240
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1236-L1240

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

theorem effective_of_winnable_and_q_reduced (G : CFGraph) (q : G.V) (D : CFDiv G) :
  winnable G D → q_reduced G q D → effective D := by sorry

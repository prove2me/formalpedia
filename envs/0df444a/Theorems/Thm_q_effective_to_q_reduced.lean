-- Prove2me | Theorems.Thm_q_effective_to_q_reduced
-- name    : q_effective_to_q_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:43:50.236646+00:00
-- url     : https://prove2.me/theorems/150132c4-ff69-4d66-8198-dbe6aa67b201
-- title:
--   q effective to q reduced: q effective to q reduced
-- statement:
--   In a connected graph, every $q$-effective divisor is linearly equivalent to a $q$-reduced
--   divisor.
--
--   The proof is by induction on `reduction_excess`.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1335-L1533
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1335-L1533

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

theorem q_effective_to_q_reduced {G : CFGraph} (h_conn : graph_connected G) {q : G.V} {D : CFDiv G} (h_eff : q_effective q D) :
  ∃ E : CFDiv G, q_reduced G q E ∧ linear_equiv G D E := by sorry

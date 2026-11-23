-- Prove2me | Theorems.Thm_winnable_iff_q_reduced_effective
-- name    : winnable_iff_q_reduced_effective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:44:59.389564+00:00
-- url     : https://prove2.me/theorems/9896daeb-6ae2-4493-8403-121015dfb2fe
-- title:
--   winnable iff q reduced effective: winnable iff q reduced effective
-- statement:
--   A divisor is winnable if and only if its $q$-reduced representative is effective.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 3.7,
--   rephrased.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1570-L1592
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1570-L1592

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

theorem winnable_iff_q_reduced_effective {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  winnable G D ↔ ∃ D' : CFDiv G, linear_equiv G D D' ∧ q_reduced G q D' ∧ effective D' := by sorry

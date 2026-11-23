-- Prove2me | Theorems.Thm_unique_q_reduced
-- name    : unique_q_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:42:35.488207+00:00
-- url     : https://prove2.me/theorems/dd325f54-d838-4c56-882d-85fd31652abc
-- title:
--   unique q reduced: unique q reduced
-- statement:
--   Every divisor is linearly equivalent to exactly one $q$-reduced divisor.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 3.6
--   (existence and uniqueness combined).
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1555-L1564
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1555-L1564

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

theorem unique_q_reduced {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  ∃! D' : CFDiv G, linear_equiv G D D' ∧ q_reduced G q D' := by sorry

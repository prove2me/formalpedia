-- Prove2me | Theorems.Thm_exists_q_reduced_representative
-- name    : exists_q_reduced_representative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:42:24.997211+00:00
-- url     : https://prove2.me/theorems/377cb41b-fbd0-4f9c-998e-62c1c3d1e4cb
-- title:
--   exists q reduced representative: exists q reduced representative
-- statement:
--   Every divisor is linearly equivalent to some $q$-reduced divisor.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 3.6,
--   part 1 (existence).
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1539-L1549
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1539-L1549

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

theorem exists_q_reduced_representative {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  ∃ D' : CFDiv G, linear_equiv G D D' ∧ q_reduced G q D' := by sorry

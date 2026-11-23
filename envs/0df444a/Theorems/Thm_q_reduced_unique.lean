-- Prove2me | Theorems.Thm_q_reduced_unique
-- name    : q_reduced_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:43:41.643146+00:00
-- url     : https://prove2.me/theorems/458d48b9-adcf-40df-bbca-c9399cd358ee
-- title:
--   q reduced unique: q reduced unique
-- statement:
--   The $q$-reduced representative of a divisor class is unique.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 3.6,
--   part 2 (uniqueness).
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1246-L1268
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1246-L1268

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

theorem q_reduced_unique (G : CFGraph) (q : G.V) (D₁ D₂ : CFDiv G) :
  q_reduced G q D₁ ∧ q_reduced G q D₂ ∧ linear_equiv G D₁ D₂ → D₁ = D₂ := by sorry

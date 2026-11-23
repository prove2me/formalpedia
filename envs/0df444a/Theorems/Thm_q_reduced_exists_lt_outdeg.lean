-- Prove2me | Theorems.Thm_q_reduced_exists_lt_outdeg
-- name    : q_reduced.exists_lt_outdeg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:42:08.32113+00:00
-- url     : https://prove2.me/theorems/a23c86a2-007d-4bfb-b0fa-1433344b6a9c
-- title:
--   q reduced: exists lt outdeg
-- statement:
--   A nonempty set avoiding `q` contains a vertex that would go into debt when fired
--   from a `q`-reduced divisor.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1066-L1070
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1066-L1070

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

theorem q_reduced.exists_lt_outdeg {G : CFGraph} {q : G.V} {D : CFDiv G}
    (hred : q_reduced G q D) {S : Finset G.V} (hq : q ∉ S) (hS : S.Nonempty) :
    ∃ v ∈ S, D v < outdeg_S G S v := by sorry

-- Prove2me | Theorems.Thm_deg_of_eff_nonneg
-- name    : deg_of_eff_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:43:15.971818+00:00
-- url     : https://prove2.me/theorems/fa722fed-b08a-4a76-a953-5521f7835502
-- title:
--   deg of eff nonneg: deg of eff nonneg
-- statement:
--   Effective divisors have nonnegative degree.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L471-L474
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L471-L474

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

theorem deg_of_eff_nonneg (D : CFDiv G) :
  effective D → deg D ≥ 0 := by sorry

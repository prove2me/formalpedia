-- Prove2me | Theorems.Thm_eff_degree_zero
-- name    : eff_degree_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:42:32.81181+00:00
-- url     : https://prove2.me/theorems/1e71ccc6-20ca-4724-afae-d8f43fcf3e14
-- title:
--   eff degree zero: eff degree zero
-- statement:
--   The only effective divisor of degree 0 is 0.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L477-L481
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L477-L481

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

theorem eff_degree_zero (D : CFDiv G) : effective D → deg D = 0 → D = 0 := by sorry

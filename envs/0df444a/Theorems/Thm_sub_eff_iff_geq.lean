-- Prove2me | Theorems.Thm_sub_eff_iff_geq
-- name    : sub_eff_iff_geq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:43:12.61439+00:00
-- url     : https://prove2.me/theorems/6ba57a0a-b354-4be1-a1c7-a387bd1c382d
-- title:
--   sub eff iff geq: sub eff iff geq
-- statement:
--   The divisor $D_1-D_2$ is effective if and only if $D_1 \ge D_2$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L433-L434
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L433-L434

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

theorem sub_eff_iff_geq {G : CFGraph} (D₁ D₂ : CFDiv G) : effective (D₁ - D₂) ↔ D₁ ≥ D₂ := by sorry

-- Prove2me | Theorems.Thm_principal_iff_eq_prin
-- name    : principal_iff_eq_prin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:41:58.168782+00:00
-- url     : https://prove2.me/theorems/1551ace6-2b37-4e53-9b4b-09089a178f33
-- title:
--   principal iff eq prin: principal iff eq prin
-- statement:
--   A divisor is principal if and only if it equals `prin G σ` for some firing script `σ`.
--   This gives a concrete characterization of the subgroup `principal_divisors G`.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L316-L396
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L316-L396

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

theorem principal_iff_eq_prin (G : CFGraph) (D : CFDiv G) :
  D ∈ principal_divisors G ↔ ∃ σ : firing_script G, D = prin G σ := by sorry

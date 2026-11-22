-- Prove2me | Theorems.Thm_abs_eq_zero_iff_zero
-- name    : abs_eq_zero_iff_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:38.43897+00:00
-- url     : https://prove2.me/theorems/5ff0422a-b5d2-4b3e-b046-498be85b88e7
-- title:
--   abs eq zero iff zero: abs eq zero iff zero
-- statement:
--   An element of a lattice-ordered group is zero iff its absolute value is zero.
--   Extends `Mathlib.Algebra.Order.Module.Basic.abs_eq_zero` to the non-total-order setting.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L53-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L53-L75

module
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable (x : X)

theorem abs_eq_zero_iff_zero : |x| = 0 ↔ x = 0 := by sorry

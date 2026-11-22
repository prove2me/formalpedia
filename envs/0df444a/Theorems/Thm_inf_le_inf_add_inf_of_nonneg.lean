-- Prove2me | Theorems.Thm_inf_le_inf_add_inf_of_nonneg
-- name    : inf_le_inf_add_inf_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:44.917225+00:00
-- url     : https://prove2.me/theorems/5afac2f0-cc07-40a1-b5b1-792d49f9fa61
-- title:
--   inf le inf add inf of nonneg: inf le inf add inf of nonneg
-- statement:
--   For non-negative `x`, `a`, `b`: `x ⊓ (a + b) ≤ x ⊓ a + x ⊓ b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L117-L135
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L117-L135

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

theorem inf_le_inf_add_inf_of_nonneg (a b : X) (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    x ⊓ (a + b) ≤ x ⊓ a + x ⊓ b := by sorry

-- Prove2me | Theorems.Thm_infinitesimal_eq_zero
-- name    : infinitesimal_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:33.486704+00:00
-- url     : https://prove2.me/theorems/73ae7e52-e317-4954-a458-2c58e8524a6e
-- title:
--   infinitesimal eq zero: infinitesimal eq zero
-- statement:
--   An element whose absolute-value multiples are bounded must be zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L478-L482
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L478-L482

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
  [VectorLattice X]
variable (x y : X)
variable [IsVLArchimedean X]
omit [VectorLattice X]

theorem infinitesimal_eq_zero {x y : X}
    (h : ∀ n : ℕ, n • |x| ≤ y) : x = 0 := by sorry

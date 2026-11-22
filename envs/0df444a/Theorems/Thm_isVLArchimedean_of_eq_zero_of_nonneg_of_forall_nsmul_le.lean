-- Prove2me | Theorems.Thm_isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
-- name    : isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:45.908804+00:00
-- url     : https://prove2.me/theorems/bf919426-66f5-4076-98c2-3a358dac4d12
-- title:
--   is VLArchimedean of eq zero of nonneg of forall nsmul le: is VLArchimedean of eq zero of nonneg of forall nsmul le
-- statement:
--   Constructor from the non-negative formulation of the Archimedean property.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L409-L416
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L409-L416

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
omit [VectorLattice X]

theorem isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
    (H : ∀ {x y : X}, 0 ≤ x → (∀ n : ℕ, n • x ≤ y) → x = 0) :
    IsVLArchimedean X := by sorry

-- Prove2me | Theorems.Thm_isVLArchimedean_iff_isGLB_inv_smul
-- name    : isVLArchimedean_iff_isGLB_inv_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:22.579463+00:00
-- url     : https://prove2.me/theorems/1c3341a5-3512-451e-aec7-a7ce2a1a1e7b
-- title:
--   is VLArchimedean iff is GLB inv smul: is VLArchimedean iff is GLB inv smul
-- statement:
--   A vector lattice is Archimedean iff for every positive `u`, the infimum of
--   `(1/n) • u` over `n ≥ 1` equals `0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L438-L472
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L438-L472

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

theorem isVLArchimedean_iff_isGLB_inv_smul :
    IsVLArchimedean X ↔
      ∀ u : X, 0 ≤ u →
        IsGLB {v : X | ∃ n : ℕ, 0 < n ∧ v = (n : ℝ)⁻¹ • u} 0 := by sorry

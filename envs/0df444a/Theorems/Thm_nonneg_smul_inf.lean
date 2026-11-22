-- Prove2me | Theorems.Thm_nonneg_smul_inf
-- name    : nonneg_smul_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:45.057775+00:00
-- url     : https://prove2.me/theorems/5bd9e414-4189-41eb-b5a2-dec4a085b038
-- title:
--   nonneg smul inf: nonneg smul inf
-- statement:
--   A non-negative scalar distributes over `⊓`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L334-L341
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L334-L341

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

theorem nonneg_smul_inf (a : ℝ) (nonneg : a ≥ 0) :
  a • (x ⊓ y) = (a • x) ⊓ (a • y) := by sorry

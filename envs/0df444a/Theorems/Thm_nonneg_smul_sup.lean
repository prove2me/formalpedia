-- Prove2me | Theorems.Thm_nonneg_smul_sup
-- name    : nonneg_smul_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:41.435287+00:00
-- url     : https://prove2.me/theorems/4802d43e-6fbe-4393-ac04-fbc89f66edad
-- title:
--   nonneg smul sup: nonneg smul sup
-- statement:
--   A non-negative scalar distributes over `⊔`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L246-L271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L246-L271

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

theorem nonneg_smul_sup (a : ℝ) (nonneg : a ≥ 0) :
  a • (x ⊔ y) = (a • x) ⊔ (a • y) := by sorry

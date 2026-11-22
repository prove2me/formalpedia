-- Prove2me | Theorems.Thm_sup_smul_nonneg
-- name    : sup_smul_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:17.179953+00:00
-- url     : https://prove2.me/theorems/5d420ea3-4284-41b4-bece-c79a7fedbd1e
-- title:
--   sup smul nonneg: sup smul nonneg
-- statement:
--   Scalar `sup` distributes over a non-negative element.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L344-L352
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L344-L352

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

theorem sup_smul_nonneg (a b : ℝ) (h : 0 ≤ x) :
    (a ⊔ b) • x = (a • x) ⊔ (b • x) := by sorry

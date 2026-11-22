-- Prove2me | Theorems.Thm_posPart_smul_nonneg
-- name    : posPart_smul_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:50.257244+00:00
-- url     : https://prove2.me/theorems/7cfe07d9-61d4-4b96-815e-17b2d325b3fd
-- title:
--   pos Part smul nonneg: pos Part smul nonneg
-- statement:
--   A non-negative scalar commutes with the positive part.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L274-L277
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L274-L277

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

theorem posPart_smul_nonneg {a : ℝ} (ha : 0 ≤ a) (x : X) :
    (a • x)⁺ = a • x⁺ := by sorry

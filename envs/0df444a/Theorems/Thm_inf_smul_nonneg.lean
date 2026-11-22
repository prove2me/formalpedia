-- Prove2me | Theorems.Thm_inf_smul_nonneg
-- name    : inf_smul_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:20.515799+00:00
-- url     : https://prove2.me/theorems/4eba0d65-de87-49e0-8693-10de5e00b60e
-- title:
--   inf smul nonneg: inf smul nonneg
-- statement:
--   Scalar `inf` distributes over a non-negative element.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L355-L363
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L355-L363

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

theorem inf_smul_nonneg (a b : ℝ) (h : 0 ≤ x) :
    (a ⊓ b) • x = (a • x) ⊓ (b • x) := by sorry

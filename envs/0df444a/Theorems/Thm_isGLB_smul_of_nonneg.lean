-- Prove2me | Theorems.Thm_isGLB_smul_of_nonneg
-- name    : isGLB_smul_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:20.242059+00:00
-- url     : https://prove2.me/theorems/2f89d46f-93e4-4449-9ced-5a6f98e2458e
-- title:
--   is GLB smul of nonneg: is GLB smul of nonneg
-- statement:
--   A non-negative scalar distributes over infima: `λ • inf A = inf (λ • A)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L307-L331
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L307-L331

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

theorem isGLB_smul_of_nonneg {A : Set X} {a : X} {lam : ℝ} (hlam : 0 ≤ lam)
    (h : IsGLB A a) : IsGLB ((fun z => lam • z) '' A) (lam • a) := by sorry

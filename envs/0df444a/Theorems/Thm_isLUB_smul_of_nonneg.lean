-- Prove2me | Theorems.Thm_isLUB_smul_of_nonneg
-- name    : isLUB_smul_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:16.448118+00:00
-- url     : https://prove2.me/theorems/f6bc487a-7744-4a58-84f0-dc55bdf749ad
-- title:
--   is LUB smul of nonneg: is LUB smul of nonneg
-- statement:
--   A non-negative scalar distributes over suprema: `λ • sup A = sup (λ • A)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L280-L304
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L280-L304

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

theorem isLUB_smul_of_nonneg {A : Set X} {a : X} {lam : ℝ} (hlam : 0 ≤ lam)
    (h : IsLUB A a) : IsLUB ((fun z => lam • z) '' A) (lam • a) := by sorry

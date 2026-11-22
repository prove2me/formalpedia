-- Prove2me | Theorems.Thm_isGLB_const_add
-- name    : isGLB_const_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:49.441666+00:00
-- url     : https://prove2.me/theorems/a7d328dd-4ea7-4312-8f13-a65a136f2d8b
-- title:
--   is GLB const add: is GLB const add
-- statement:
--   Translation preserves infima: `x + inf A = inf(x + A)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L143-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L143-L145

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
variable (x : X)

theorem isGLB_const_add {A : Set X} {a : X} (x : X) (h : IsGLB A a) :
    IsGLB ((fun z => x + z) '' A) (x + a) := by sorry

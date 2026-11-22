-- Prove2me | Theorems.Thm_isGLB_sup_const
-- name    : isGLB_sup_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:50.90088+00:00
-- url     : https://prove2.me/theorems/4d3c9303-94c9-410d-bc87-02329e2d8187
-- title:
--   is GLB sup const: is GLB sup const
-- statement:
--   Join distributes over arbitrary infima: `x ⊔ inf A = inf {x ⊔ a : a ∈ A}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L167-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L167-L183

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

theorem isGLB_sup_const {A : Set X} {a : X} (x : X) (h : IsGLB A a) :
    IsGLB ((fun z => x ⊔ z) '' A) (x ⊔ a) := by sorry

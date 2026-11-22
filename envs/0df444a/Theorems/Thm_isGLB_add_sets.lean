-- Prove2me | Theorems.Thm_isGLB_add_sets
-- name    : isGLB_add_sets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:13.781348+00:00
-- url     : https://prove2.me/theorems/ea6de603-570d-48ba-a959-01cd6b159807
-- title:
--   is GLB add sets: is GLB add sets
-- statement:
--   `inf(A + B) = inf A + inf B`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L186-L203
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L186-L203

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

theorem isGLB_add_sets {A B : Set X} {a b : X}
    (hA : IsGLB A a) (hB : IsGLB B b) :
    IsGLB ((fun p : X × X => p.1 + p.2) '' (A ×ˢ B)) (a + b) := by sorry

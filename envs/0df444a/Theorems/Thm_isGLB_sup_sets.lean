-- Prove2me | Theorems.Thm_isGLB_sup_sets
-- name    : isGLB_sup_sets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:16.204806+00:00
-- url     : https://prove2.me/theorems/3832a2ec-ac1d-4401-a94e-653186f5bef7
-- title:
--   is GLB sup sets: is GLB sup sets
-- statement:
--   `inf(A ∨ B) = inf A ∨ inf B`, where `A ∨ B = {p ⊔ q : p ∈ A, q ∈ B}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L206-L221
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L206-L221

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

theorem isGLB_sup_sets {A B : Set X} {a b : X}
    (hA : IsGLB A a) (hB : IsGLB B b) :
    IsGLB ((fun p : X × X => p.1 ⊔ p.2) '' (A ×ˢ B)) (a ⊔ b) := by sorry

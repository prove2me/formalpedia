-- Prove2me | Theorems.Thm_isLUB_inf_const
-- name    : isLUB_inf_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:54.373455+00:00
-- url     : https://prove2.me/theorems/825feca6-b7c7-4e09-924f-c973a62fe935
-- title:
--   is LUB inf const: is LUB inf const
-- statement:
--   Meet distributes over arbitrary suprema: `x ⊓ sup A = sup {x ⊓ a : a ∈ A}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L148-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L148-L164

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

theorem isLUB_inf_const {A : Set X} {a : X} (x : X) (h : IsLUB A a) :
    IsLUB ((fun z => x ⊓ z) '' A) (x ⊓ a) := by sorry

-- Prove2me | Theorems.Thm_sub_inf_eq_posPart
-- name    : sub_inf_eq_posPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:42.354954+00:00
-- url     : https://prove2.me/theorems/e37386bb-b103-4272-ae30-717a6efbdb58
-- title:
--   sub inf eq pos Part: sub inf eq pos Part
-- statement:
--   `x - x ⊓ y = (x - y)⁺`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L98-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L98-L99

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

theorem sub_inf_eq_posPart (y : X) : x - x ⊓ y = (x - y)⁺ := by sorry

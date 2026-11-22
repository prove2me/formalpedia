-- Prove2me | Theorems.Thm_inf_eq_sub_posPart
-- name    : inf_eq_sub_posPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:45.314391+00:00
-- url     : https://prove2.me/theorems/70341e68-5bea-4bcc-b3c3-b66e4d38afbe
-- title:
--   inf eq sub pos Part: inf eq sub pos Part
-- statement:
--   `x ⊓ y = x - (x - y)⁺`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L93-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L93-L95

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

theorem inf_eq_sub_posPart (y : X) : x ⊓ y = x - (x - y)⁺ := by sorry

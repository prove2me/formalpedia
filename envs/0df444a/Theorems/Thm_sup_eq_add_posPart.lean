-- Prove2me | Theorems.Thm_sup_eq_add_posPart
-- name    : sup_eq_add_posPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:48.192231+00:00
-- url     : https://prove2.me/theorems/7bdb90f0-bc2f-4fb1-8d5f-b98ab1ad2ac6
-- title:
--   sup eq add pos Part: sup eq add pos Part
-- statement:
--   `x ⊔ y = x + (y - x)⁺`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L89-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L89-L90

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

theorem sup_eq_add_posPart (y : X) : x ⊔ y = x + (y - x)⁺ := by sorry

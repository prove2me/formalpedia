-- Prove2me | Theorems.Thm_inf_eq_zero_of_isVLDisjoint
-- name    : inf_eq_zero_of_isVLDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:25.005783+00:00
-- url     : https://prove2.me/theorems/faebc518-1a43-4194-9707-2f4ea9d8b433
-- title:
--   inf eq zero of is VLDisjoint: inf eq zero of is VLDisjoint
-- statement:
--   Disjoint positive elements satisfy `x ⊓ y = 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L56-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L56-L58

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem inf_eq_zero_of_isVLDisjoint {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : IsVLDisjoint x y) : x ⊓ y = 0 := by sorry

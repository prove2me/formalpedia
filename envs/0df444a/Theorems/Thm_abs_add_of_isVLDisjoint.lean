-- Prove2me | Theorems.Thm_abs_add_of_isVLDisjoint
-- name    : abs_add_of_isVLDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:37.826796+00:00
-- url     : https://prove2.me/theorems/76110d42-afd3-4b92-a3b4-a251e76f03bf
-- title:
--   abs add of is VLDisjoint: abs add of is VLDisjoint
-- statement:
--   If `x ⊥ y` then `|x + y| = |x| + |y|` (Birkhoff identity).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L92-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L92-L154

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem abs_add_of_isVLDisjoint {x y : X} (h : IsVLDisjoint x y) :
    |x + y| = |x| + |y| := by sorry

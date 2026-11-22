-- Prove2me | Theorems.Thm_isVLDisjoint_comm
-- name    : isVLDisjoint_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:14.039358+00:00
-- url     : https://prove2.me/theorems/4bb5fdce-e32e-4fba-9cf5-dccfc8e88dce
-- title:
--   is VLDisjoint comm: is VLDisjoint comm
-- statement:
--   The is VLDisjoint comm construction uses the is VLDisjoint comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L43-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L43-L45

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
omit [IsOrderedAddMonoid X]

theorem isVLDisjoint_comm {x y : X} :
    IsVLDisjoint x y ↔ IsVLDisjoint y x := by sorry

-- Prove2me | Theorems.Thm_isVLDisjoint_posPart_sub_smul
-- name    : isVLDisjoint_posPart_sub_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:17:16.593726+00:00
-- url     : https://prove2.me/theorems/e78b7619-f762-4d2a-bff8-de6c0849807a
-- title:
--   is VLDisjoint pos Part sub smul: is VLDisjoint pos Part sub smul
-- statement:
--   For any `x, y` and `λ > 0`, the positive parts `(x - λ • y)⁺` and
--   `(y - λ⁻¹ • x)⁺` are disjoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L401-L409
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L401-L409

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

theorem isVLDisjoint_posPart_sub_smul (x y : X) {lam : ℝ} (hlam : 0 < lam) :
    IsVLDisjoint (x - lam • y)⁺ (y - lam⁻¹ • x)⁺ := by sorry

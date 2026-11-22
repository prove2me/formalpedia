-- Prove2me | Theorems.Thm_isVLDisjoint_decomposition_unique
-- name    : isVLDisjoint_decomposition_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:49.113805+00:00
-- url     : https://prove2.me/theorems/ba7c9305-fe19-4975-9123-64e8d71e9fc9
-- title:
--   is VLDisjoint decomposition unique: is VLDisjoint decomposition unique
-- statement:
--   Disjoint decomposition is unique: if `x = u₁ - v₁ = u₂ - v₂` with
--   `u₁ ⊥ v₁` and `u₂ ⊥ v₂` (all non-negative), then `u₁ = u₂` and
--   `v₁ = v₂`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L70-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L70-L83

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem isVLDisjoint_decomposition_unique {u₁ v₁ u₂ v₂ : X}
    (hu₁ : 0 ≤ u₁) (hv₁ : 0 ≤ v₁) (hu₂ : 0 ≤ u₂) (hv₂ : 0 ≤ v₂)
    (hd₁ : IsVLDisjoint u₁ v₁) (hd₂ : IsVLDisjoint u₂ v₂)
    (h : u₁ - v₁ = u₂ - v₂) : u₁ = u₂ ∧ v₁ = v₂ := by sorry

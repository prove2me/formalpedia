-- Prove2me | Theorems.Thm_isVLDisjoint_finset_sum
-- name    : isVLDisjoint_finset_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:46.705025+00:00
-- url     : https://prove2.me/theorems/21ea3fb5-1e66-4d11-9668-c410a027ebfe
-- title:
--   is VLDisjoint finset sum: is VLDisjoint finset sum
-- statement:
--   A sum of elements disjoint from a fixed element remains disjoint from it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L289-L297
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L289-L297

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem isVLDisjoint_finset_sum {ι : Type*} {s : Finset ι} {x : X} {f : ι → X}
    (h : ∀ i ∈ s, IsVLDisjoint x (f i)) : IsVLDisjoint x (∑ i ∈ s, f i) := by sorry

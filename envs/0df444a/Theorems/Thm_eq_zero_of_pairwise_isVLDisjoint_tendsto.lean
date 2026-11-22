-- Prove2me | Theorems.Thm_eq_zero_of_pairwise_isVLDisjoint_tendsto
-- name    : eq_zero_of_pairwise_isVLDisjoint_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:17:15.068232+00:00
-- url     : https://prove2.me/theorems/146fdb14-21ba-4acc-93a4-96f1de60cd66
-- title:
--   eq zero of pairwise is VLDisjoint tendsto: eq zero of pairwise is VLDisjoint tendsto
-- statement:
--   In a normed vector lattice, a limit of a pairwise-disjoint sequence is
--   zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L605-L634
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L605-L634

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset

theorem eq_zero_of_pairwise_isVLDisjoint_tendsto {Y : Type*}
    [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] {u : ℕ → Y} {x : Y}
    (hdisj : Pairwise fun i j => IsVLDisjoint (u i) (u j))
    (hlim : Tendsto u atTop (𝓝 x)) : x = 0 := by sorry

-- Prove2me | Theorems.Thm_isometry_coe_completion
-- name    : isometry_coe_completion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:14:46.035687+00:00
-- url     : https://prove2.me/theorems/a334bd77-7a90-4307-afc1-ae400ee4c1b1
-- title:
--   isometry coe completion: isometry coe completion
-- statement:
--   The canonical inclusion into the completion preserves the isometry to `toComplₗᵢ`; it is
--   an isometry from `X` into its completion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L400-L402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Normed.lean#L400-L402

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
set_option autoImplicit true
@[expose] public section
public section
open UniformSpace
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

theorem isometry_coe_completion : Isometry ((↑) : X → Completion X) := by sorry

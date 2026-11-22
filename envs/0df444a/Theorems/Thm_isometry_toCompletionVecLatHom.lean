-- Prove2me | Theorems.Thm_isometry_toCompletionVecLatHom
-- name    : isometry_toCompletionVecLatHom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:15.908711+00:00
-- url     : https://prove2.me/theorems/e494640f-3431-4a55-a22e-0fb0d314c3bf
-- title:
--   isometry to Completion Vec Lat Hom: isometry to Completion Vec Lat Hom
-- statement:
--   The canonical inclusion of a normed vector lattice into its completion is an isometry;
--   together with `toCompletionVecLatHom` this exhibits the inclusion as a lattice isometry.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L536-L539
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L536-L539

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]
open UniformSpace
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

theorem isometry_toCompletionVecLatHom :
    Isometry (toCompletionVecLatHom : X → Completion X) := by sorry

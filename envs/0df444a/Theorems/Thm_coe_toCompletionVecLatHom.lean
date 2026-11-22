-- Prove2me | Theorems.Thm_coe_toCompletionVecLatHom
-- name    : coe_toCompletionVecLatHom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:15.33834+00:00
-- url     : https://prove2.me/theorems/4efddb53-5206-4dcd-9465-01f4cbe61b4b
-- title:
--   coe to Completion Vec Lat Hom: coe to Completion Vec Lat Hom
-- statement:
--   The coe to Completion Vec Lat Hom construction uses the coe to Completion Vec Lat Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L530-L532
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L530-L532

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

theorem coe_toCompletionVecLatHom :
    ⇑(toCompletionVecLatHom : VecLatHom X (Completion X)) = ((↑) : X → Completion X) := by sorry

attribute [defeq] coe_toCompletionVecLatHom

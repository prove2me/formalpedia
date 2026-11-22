-- Prove2me | Theorems.Thm_ldim_versionSpace_le
-- name    : ldim_versionSpace_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:40:17.750442+00:00
-- url     : https://prove2.me/theorems/3ea25890-a2fe-4e25-8295-2d5dd6d4ff35
-- title:
--   ldim version Space le: ldim version Space le
-- statement:
--   Ldim of version space ≤ Ldim of C.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L196-L200
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L196-L200

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
set_option autoImplicit true
@[expose] public section
public section

theorem ldim_versionSpace_le {X : Type} {C : ConceptClass X Bool}
    {history : List (X × Bool)} :
    LittlestoneDim X (versionSpace C history) ≤ LittlestoneDim X C := by sorry

-- Prove2me | Theorems.Thm_boolToSign_abs_le_one
-- name    : boolToSign_abs_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:38:00.324131+00:00
-- url     : https://prove2.me/theorems/2a12f275-2056-4716-87ec-36c0131f6806
-- title:
--   bool To Sign abs le one: bool To Sign abs le one
-- statement:
--   The bool To Sign abs le one construction uses the bool To Sign abs le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L39-L40
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L39-L40

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem boolToSign_abs_le_one (b : Bool) : |boolToSign b| ≤ 1 := by sorry

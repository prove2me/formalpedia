-- Prove2me | Theorems.Thm_boolToSign_mul_abs_le_one
-- name    : boolToSign_mul_abs_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:59.296097+00:00
-- url     : https://prove2.me/theorems/04b8322b-ff30-4291-bc59-fdeaf160b889
-- title:
--   bool To Sign mul abs le one: bool To Sign mul abs le one
-- statement:
--   The bool To Sign mul abs le one construction uses the bool To Sign mul abs le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L48-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L48-L49

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem boolToSign_mul_abs_le_one (b₁ b₂ : Bool) : |boolToSign b₁ * boolToSign b₂| ≤ 1 := by sorry

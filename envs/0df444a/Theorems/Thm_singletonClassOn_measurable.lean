-- Prove2me | Theorems.Thm_singletonClassOn_measurable
-- name    : singletonClassOn_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:42:10.720193+00:00
-- url     : https://prove2.me/theorems/d4a31e46-a6f3-4c01-8df5-bb3a5d936cda
-- title:
--   singleton Class On measurable: singleton Class On measurable
-- statement:
--   Every hypothesis in `singletonClassOn A` is Borel measurable: `zeroConcept` is
--   constant, and each `singletonConcept a` factors through `measurableSet_singleton`. The
--   class is regular at the level of individual hypotheses; non-measurability enters only
--   through the existential over `A`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L85-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L85-L93

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_BorelAnalyticSeparation
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory

theorem singletonClassOn_measurable
    (A : Set ℝ) :
    ∀ h ∈ singletonClassOn A, Measurable h := by sorry

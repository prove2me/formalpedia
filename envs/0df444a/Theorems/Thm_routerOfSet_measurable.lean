-- Prove2me | Theorems.Thm_routerOfSet_measurable
-- name    : routerOfSet_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:08.850538+00:00
-- url     : https://prove2.me/theorems/2f889b6d-85fe-4458-b37e-cd4337d6a34c
-- title:
--   router Of Set measurable: router Of Set measurable
-- statement:
--   The router for a fixed measurable set is jointly measurable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L85-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L85-L89

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem routerOfSet_measurable {X : Type u} [MeasurableSpace X]
    {A : Set X} (hA : MeasurableSet A) :
    Measurable (fun p : Unit × X => routerOfSet A p.1 p.2) := by sorry

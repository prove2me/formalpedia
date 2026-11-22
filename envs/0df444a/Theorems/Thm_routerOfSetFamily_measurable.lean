-- Prove2me | Theorems.Thm_routerOfSetFamily_measurable
-- name    : routerOfSetFamily_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:06.361903+00:00
-- url     : https://prove2.me/theorems/4e806277-c013-4927-85af-a269f5b577c8
-- title:
--   router Of Set Family measurable: router Of Set Family measurable
-- statement:
--   The router for a countable measurable family is jointly measurable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L92-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L92-L102

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

theorem routerOfSetFamily_measurable {X : Type u} [MeasurableSpace X]
    {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n)) :
    Measurable (fun p : ℕ × X => routerOfSetFamily A p.1 p.2) := by sorry

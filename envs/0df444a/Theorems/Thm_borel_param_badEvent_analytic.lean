-- Prove2me | Theorems.Thm_borel_param_badEvent_analytic
-- name    : borel_param_badEvent_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:01.474311+00:00
-- url     : https://prove2.me/theorems/eb75c63a-11ac-4a42-95a9-45a25fa83ac6
-- title:
--   borel param bad Event analytic: borel param bad Event analytic
-- statement:
--   The bad event (projection of witness set) is analytic.
--       Projection of a Borel set from a StandardBorelSpace is analytic (Suslin).
--       This is the key step: existential quantification over parameters
--       produces an analytic (Σ₁¹) set, which may not be Borel.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L137-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L137-L154

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory

theorem borel_param_badEvent_analytic
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2))
    (c : Concept X Bool) (hc : Measurable c)
    (m : ℕ) (ε : ℝ) :
    MeasureTheory.AnalyticSet (paramBadEvent e c m ε) := by sorry

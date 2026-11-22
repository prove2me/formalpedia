-- Prove2me | Theorems.Thm_borel_param_wellBehavedVCMeasTarget
-- name    : borel_param_wellBehavedVCMeasTarget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:45.109794+00:00
-- url     : https://prove2.me/theorems/e3f3d917-43cd-40d2-9b7b-a9d4b63eeeda
-- title:
--   borel param well Behaved VCMeas Target: borel param well Behaved VCMeas Target
-- statement:
--   Class-level corollary: every Borel-parameterized concept class with a measurable
--   evaluation map satisfies `WellBehavedVCMeasTarget`. Composes
--   `borel_param_nullMeasurableSet_bad_event` over all measurable targets `c`. The
--   measurable-target variant of `WellBehavedVC` is what the kernel actually proves; the
--   unrestricted variant remains open and is the subject of the Borel-analytic separation
--   witness in `Theorem/BorelAnalyticSeparation.lean`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L209-L230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L209-L230

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

theorem borel_param_wellBehavedVCMeasTarget
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2)) :
    WellBehavedVCMeasTarget X (Set.range e) := by sorry

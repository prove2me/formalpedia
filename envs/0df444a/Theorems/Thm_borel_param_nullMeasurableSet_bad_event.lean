-- Prove2me | Theorems.Thm_borel_param_nullMeasurableSet_bad_event
-- name    : borel_param_nullMeasurableSet_bad_event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:18.725867+00:00
-- url     : https://prove2.me/theorems/4c311b4a-6cf1-48f7-8fa6-3d29d1d83aca
-- title:
--   borel param null Measurable Set bad event: borel param null Measurable Set bad event
-- statement:
--   Positive bridge. If a concept class is parameterized by a Borel measurable map
--   `Θ → Concept X` from a standard Borel space `Θ`, then the symmetrization bad event is
--   analytic, hence `NullMeasurableSet`. The bad event is a Suslin projection of a Borel
--   witness set (the projection along `Θ` of `{(θ, p) | gap(eval θ, p) ≥ ε / 2}`), and
--   projections of Borel sets are analytic by definition. This is the entry point through
--   which Borel parameterization implies the regularity required by the fundamental
--   theorem.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L189-L199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L189-L199

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

theorem borel_param_nullMeasurableSet_bad_event
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2))
    (c : Concept X Bool) (hc : Measurable c)
    (m : ℕ) (ε : ℝ)
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    NullMeasurableSet (paramBadEvent e c m ε) (GhostPairMeasure D m) := by sorry

-- Prove2me | Theorems.Thm_formalLearning_analyticSet_nullMeasurableSet_ghostPairs
-- name    : formalLearning_analyticSet_nullMeasurableSet_ghostPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:01.603038+00:00
-- url     : https://prove2.me/theorems/9b857436-1de4-4b76-9a28-9ca3b1b925ee
-- title:
--   formal Learning analytic Set null Measurable Set ghost Pairs: formal Learning analytic Set null Measurable Set ghost Pairs
-- statement:
--   Analytic subsets of the ghost sample space `(Fin m → X) × (Fin m → X)` are
--   `NullMeasurableSet` under the product probability measure. A specialisation of
--   `formalLearning_analyticSet_nullMeasurableSet` from `PureMath/AnalyticMeasurability.lean` to the type
--   the symmetrization argument actually consumes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L170-L178
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/BorelAnalyticBridge.lean#L170-L178

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

theorem formalLearning_analyticSet_nullMeasurableSet_ghostPairs
    {X : Type u}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
    {m : ℕ} {s : Set ((Fin m → X) × (Fin m → X))}
    (hs : MeasureTheory.AnalyticSet s)
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    MeasureTheory.NullMeasurableSet s (GhostPairMeasure D m) := by sorry

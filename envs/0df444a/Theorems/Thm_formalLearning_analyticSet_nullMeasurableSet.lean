-- Prove2me | Theorems.Thm_formalLearning_analyticSet_nullMeasurableSet
-- name    : formalLearning_analyticSet_nullMeasurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:09.939797+00:00
-- url     : https://prove2.me/theorems/fbb25d37-c89a-4f7f-8af7-b4f3da885494
-- title:
--   formal Learning analytic Set null Measurable Set: formal Learning analytic Set null Measurable Set
-- statement:
--   **Analytic sets are null-measurable.** For any finite Borel measure on a Polish
--   space, every analytic set is `NullMeasurableSet`. The proof inner-approximates the
--   analytic set by compacts via the previous lemma, takes the union of approximators (a
--   Borel set), and shows the difference is contained in a Borel null set.
--
--   This is the abstract result that the entire Borel-analytic measurability layer of the
--   kernel rests on. The learning-theoretic significance is that the symmetrization bad
--   event, which is analytic in the Borel-parameterized setting, is automatically
--   null-measurable; this is enough to run the symmetrization argument under
--   `NullMeasurableSet` regularity, sidestepping the stronger `MeasurableSet` requirement of
--   the existing literature. Candidate for upstream contribution to Mathlib.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/AnalyticMeasurability.lean#L92-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/AnalyticMeasurability.lean#L92-L115

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
public import Mathlib.MeasureTheory.Measure.Real
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set

theorem formalLearning_analyticSet_nullMeasurableSet
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    MeasureTheory.NullMeasurableSet s μ := by sorry

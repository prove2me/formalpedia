-- Prove2me | Theorems.Thm_uniformMeasure_isProbability
-- name    : uniformMeasure_isProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:40.420811+00:00
-- url     : https://prove2.me/theorems/760e788b-77f0-46d2-9251-7b7e6e8dadf0
-- title:
--   uniform Measure is Probability: uniform Measure is Probability
-- statement:
--   The uniform measure is a probability measure when X is nonempty and finite.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1372-L1382
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1372-L1382

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem uniformMeasure_isProbability (X : Type u) [MeasurableSpace X] [Fintype X]
    (hne : Nonempty X) (hpos : 0 < Fintype.card X) :
    MeasureTheory.IsProbabilityMeasure (uniformMeasure X hne) := by sorry

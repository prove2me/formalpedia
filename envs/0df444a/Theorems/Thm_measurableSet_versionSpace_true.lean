-- Prove2me | Theorems.Thm_measurableSet_versionSpace_true
-- name    : measurableSet_versionSpace_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:52.14919+00:00
-- url     : https://prove2.me/theorems/e9aa3155-15eb-4407-9d16-a1b45df75885
-- title:
--   measurable Set version Space true: measurable Set version Space true
-- statement:
--   The preimage of {true} under the evaluation map is measurable.
--       Core lemma: decompose as countable union of measurable rectangles.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/VersionSpace.lean#L131-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/VersionSpace.lean#L131-L166

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_VersionSpace
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set

theorem measurableSet_versionSpace_true
    {X : Type u} [MeasurableSpace X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n))
    (m : ℕ) :
    MeasurableSet ((fun p : (Fin m → X × Bool) × X =>
      (versionSpaceLearner enum).learn p.1 p.2) ⁻¹' {true}) := by sorry

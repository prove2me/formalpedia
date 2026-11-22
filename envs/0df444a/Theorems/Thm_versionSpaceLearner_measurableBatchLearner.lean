-- Prove2me | Theorems.Thm_versionSpaceLearner_measurableBatchLearner
-- name    : versionSpaceLearner_measurableBatchLearner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:51.234603+00:00
-- url     : https://prove2.me/theorems/499c6066-fa51-4ab7-84c3-da4369e15d3d
-- title:
--   version Space Learner measurable Batch Learner: version Space Learner measurable Batch Learner
-- statement:
--   **Version space learners are MeasurableBatchLearners.**
--
--       For any measurable enumeration of concepts, the learner that selects
--       the first consistent hypothesis satisfies joint measurability.
--       This makes version space learners valid RL policy classes.
--
--       Proof: `measurable_to_countable'` reduces to showing each singleton
--       preimage is MeasurableSet. For `{true}`, decompose as ⋃ₙ (Aₙ ×ˢ Bₙ).
--       For `{false}`, take the complement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/VersionSpace.lean#L179-L199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/VersionSpace.lean#L179-L199

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

theorem versionSpaceLearner_measurableBatchLearner
    {X : Type u} [MeasurableSpace X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n)) :
    MeasurableBatchLearner X (versionSpaceLearner enum) := by sorry

-- Prove2me | Theorems.Thm_measurableSet_isConsistent
-- name    : measurableSet_isConsistent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:39.888802+00:00
-- url     : https://prove2.me/theorems/378e0649-3f9f-41a6-be5e-0a89f828e137
-- title:
--   measurable Set is Consistent: measurable Set is Consistent
-- statement:
--   Each "enum n is consistent with S" event is measurable in S.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/VersionSpace.lean#L89-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/VersionSpace.lean#L89-L101

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

theorem measurableSet_isConsistent
    {X : Type u} [MeasurableSpace X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n))
    (m : ℕ) (n : ℕ) :
    MeasurableSet {S : Fin m → X × Bool | IsSampleConsistent (enum n) S} := by sorry

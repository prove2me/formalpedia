-- Prove2me | Theorems.Thm_measurableSet_isFirstConsistent
-- name    : measurableSet_isFirstConsistent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:36.37808+00:00
-- url     : https://prove2.me/theorems/f233110d-85ae-4ba7-ad9d-c7a33172cd6d
-- title:
--   measurable Set is First Consistent: measurable Set is First Consistent
-- statement:
--   The "first consistent index is n" event is measurable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/VersionSpace.lean#L104-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/VersionSpace.lean#L104-L119

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

theorem measurableSet_isFirstConsistent
    {X : Type u} [MeasurableSpace X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n))
    (m : ℕ) (n : ℕ) :
    MeasurableSet {S : Fin m → X × Bool | IsFirstConsistent enum S n} := by sorry

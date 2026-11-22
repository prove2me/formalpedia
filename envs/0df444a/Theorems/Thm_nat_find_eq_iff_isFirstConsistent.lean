-- Prove2me | Theorems.Thm_nat_find_eq_iff_isFirstConsistent
-- name    : nat_find_eq_iff_isFirstConsistent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:50.360104+00:00
-- url     : https://prove2.me/theorems/c5e66d2a-fe8e-4e0d-911a-392868a11169
-- title:
--   nat find eq iff is First Consistent: nat find eq iff is First Consistent
-- statement:
--   Bridge: `Nat.find h = n ↔ IsFirstConsistent`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/VersionSpace.lean#L122-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/VersionSpace.lean#L122-L127

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

theorem nat_find_eq_iff_isFirstConsistent
    {X : Type u} (enum : ℕ → Concept X Bool)
    {m : ℕ} (S : Fin m → X × Bool)
    (h : ∃ n, IsSampleConsistent (enum n) S) (n : ℕ) :
    Nat.find h = n ↔ IsFirstConsistent enum S n := by sorry

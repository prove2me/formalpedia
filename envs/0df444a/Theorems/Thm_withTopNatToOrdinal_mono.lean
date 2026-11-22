-- Prove2me | Theorems.Thm_withTopNatToOrdinal_mono
-- name    : withTopNatToOrdinal_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:39:18.989873+00:00
-- url     : https://prove2.me/theorems/faf611dc-d09b-4d0d-b8b5-f826afac3c0f
-- title:
--   with Top Nat To Ordinal mono: with Top Nat To Ordinal mono
-- statement:
--   The embedding preserves order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L512-L523
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L512-L523

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem withTopNatToOrdinal_mono :
    ∀ a b : WithTop ℕ, a ≤ b → withTopNatToOrdinal a ≤ withTopNatToOrdinal b := by sorry

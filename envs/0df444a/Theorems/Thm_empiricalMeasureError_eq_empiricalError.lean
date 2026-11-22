-- Prove2me | Theorems.Thm_empiricalMeasureError_eq_empiricalError
-- name    : empiricalMeasureError_eq_empiricalError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:34.278392+00:00
-- url     : https://prove2.me/theorems/9ee7b682-2620-4ac0-ac35-2e4bdba29aab
-- title:
--   empirical Measure Error eq empirical Error: empirical Measure Error eq empirical Error
-- statement:
--   The empirical Measure Error eq empirical Error construction uses the empirical Measure Error eq empirical Error property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L246-L273
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L246-L273

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

theorem empiricalMeasureError_eq_empiricalError (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (h : Concept X Bool) (c : Concept X Bool)
    {m : ℕ} (hm : 0 < m) (xs : Fin m → X) :
    (EmpiricalMeasureError X h c xs).toReal =
      EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) := by sorry

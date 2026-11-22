-- Prove2me | Theorems.Thm_consistent_tail_bound
-- name    : consistent_tail_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:43.225098+00:00
-- url     : https://prove2.me/theorems/218bd954-50f6-4a12-8f2e-339dffd030cb
-- title:
--   consistent tail bound: consistent tail bound
-- statement:
--   One-sided Hoeffding: for a fixed h with TrueError(h,c,D) = p > ε,
--       the probability that h is consistent on all m IID samples is ≤ (1-ε)^m.
--
--       This is the Google formal-ml route (pac_finite_bound, nnreal_exp_bound2).
--       Each sample point xᵢ ∈ {x | h(x) = c(x)} with probability 1-p ≤ 1-ε.
--       IID: Pr[all m correct] = (1-p)^m ≤ (1-ε)^m.
--
--       Mathlib: Real.one_sub_div_pow_le_exp_neg gives (1-ε)^m ≤ exp(-εm).
--
--       This is SIMPLER than McDiarmid (one-sided, no expectation computation).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L507-L532
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L507-L532

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

theorem consistent_tail_bound {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (m : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (herr : D { x | h x ≠ c x } ≥ ENNReal.ofReal ε)
    (hmeas : MeasurableSet { x | h x ≠ c x }) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { xs : Fin m → X | ∀ i, h (xs i) = c (xs i) }
      ≤ ENNReal.ofReal ((1 - ε) ^ m) := by sorry

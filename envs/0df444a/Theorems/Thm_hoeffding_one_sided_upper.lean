-- Prove2me | Theorems.Thm_hoeffding_one_sided_upper
-- name    : hoeffding_one_sided_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:37.865259+00:00
-- url     : https://prove2.me/theorems/f8fea8bb-26ed-4db1-acf3-3ba44b2f6002
-- title:
--   hoeffding one sided upper: hoeffding one sided upper
-- statement:
--   Upper-tail Hoeffding: for iid Bernoulli(p) draws, the empirical average
--       overshoots the mean by ≥ t with probability ≤ exp(-2mt²).
--
--       This is the mirror of `hoeffding_one_sided` (which bounds the lower tail).
--       The proof uses the same sub-Gaussian machinery with Z_i = indicator(x_i) - p
--       (instead of p - indicator(x_i)).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1098-L1156
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1098-L1156

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal

theorem hoeffding_one_sided_upper {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (m : ℕ) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (_ht1 : t ≤ 1)
    (hmeas : MeasurableSet {x | h x ≠ c x}) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
        (zeroOneLoss Bool) ≥ TrueErrorReal X h c D + t}
    ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := by sorry

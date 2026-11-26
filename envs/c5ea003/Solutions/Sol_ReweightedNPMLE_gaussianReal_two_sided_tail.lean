-- Prove2me | solution 1 for ReweightedNPMLE.gaussianReal_two_sided_tail
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:07:26.256392+00:00
-- url     : https://prove2.me/submissions/bc6210bd-5c29-4fdb-a931-7a6e13f46215

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Theorems.Thm_ReweightedNPMLE_exponential_markov_lower
import Theorems.Thm_ReweightedNPMLE_exponential_markov_upper

/-!
# Gaussian radius bounds

Chernoff and finite-union estimates for the radius event in the likelihood-net
argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The standard one-dimensional Gaussian two-sided Chernoff bound. -/
theorem solution {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1).real {x : ℝ | |x| > t} ≤
      2 * Real.exp (-t ^ 2 / 2) := by
  have hmgfPos :
      ∫ x : ℝ, Real.exp (t * x) ∂gaussianReal 0 1 =
        Real.exp (t ^ 2 / 2) := by
    change mgf id (gaussianReal 0 1) t = _
    rw [mgf_id_gaussianReal]
    norm_num
  have hmgfNeg :
      ∫ x : ℝ, Real.exp (-t * x) ∂gaussianReal 0 1 =
        Real.exp (t ^ 2 / 2) := by
    change mgf id (gaussianReal 0 1) (-t) = _
    rw [mgf_id_gaussianReal]
    norm_num
  have hu := exponential_markov_upper (gaussianReal 0 1) id ht
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t) (c := t)
  have hl := exponential_markov_lower (gaussianReal 0 1) id ht
    (by simpa only [id_eq] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-t))) (c := t)
  simp only [id_eq] at hu hl
  rw [hmgfPos] at hu
  rw [hmgfNeg] at hl
  have hu' : (gaussianReal 0 1).real {x : ℝ | t ≤ x} ≤
      Real.exp (-t ^ 2 / 2) := by
    calc
      _ ≤ Real.exp (-t * t) * Real.exp (t ^ 2 / 2) := hu
      _ = Real.exp (-t ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hl' : (gaussianReal 0 1).real {x : ℝ | x ≤ -t} ≤
      Real.exp (-t ^ 2 / 2) := by
    calc
      _ ≤ Real.exp (-t * t) * Real.exp (t ^ 2 / 2) := hl
      _ = Real.exp (-t ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hsubset : {x : ℝ | |x| > t} ⊆
      {x : ℝ | t ≤ x} ∪ {x : ℝ | x ≤ -t} := by
    intro x hx
    change t < |x| at hx
    change (t ≤ x) ∨ (x ≤ -t)
    by_cases hx0 : 0 ≤ x
    · left
      rw [abs_of_nonneg hx0] at hx
      exact hx.le
    · right
      have hxneg : x < 0 := lt_of_not_ge hx0
      rw [abs_of_neg hxneg] at hx
      linarith
  calc
    (gaussianReal 0 1).real {x : ℝ | |x| > t} ≤
        (gaussianReal 0 1).real
          ({x : ℝ | t ≤ x} ∪ {x : ℝ | x ≤ -t}) :=
      measureReal_mono hsubset (by finiteness)
    _ ≤ (gaussianReal 0 1).real {x : ℝ | t ≤ x} +
        (gaussianReal 0 1).real {x : ℝ | x ≤ -t} := measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / 2) + Real.exp (-t ^ 2 / 2) := add_le_add hu' hl'
    _ = 2 * Real.exp (-t ^ 2 / 2) := by ring

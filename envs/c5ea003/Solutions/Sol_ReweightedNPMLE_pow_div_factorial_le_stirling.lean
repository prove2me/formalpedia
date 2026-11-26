-- Prove2me | solution 1 for ReweightedNPMLE.pow_div_factorial_le_stirling
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:06:30.745602+00:00
-- url     : https://prove2.me/submissions/c70649c0-fee5-4329-b66c-fbd44b2b2bde

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianNearMLE
import Definitions.Def_ReweightedNPMLE_GaussianNearMLERate
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Explicit entropy arithmetic for the Gaussian near-MLE theorem

This module turns the finite Gaussian-mixture net cardinality appearing in
`GaussianNearMLE` into the binomial and logarithmic bounds used in the
paper's rate calculation.  It is kept separate from the probabilistic
argument so that the remaining asymptotic tuning can use a small, explicit
arithmetic interface.
-/

open scoped ENNReal
open Filter Topology MeasureTheory Set

open ReweightedNPMLE
open ReweightedNPMLE in
/-- A convenient consequence of Stirling's global lower bound.  It is the
factorial estimate used for both Taylor remainders in the Gaussian net. -/
theorem solution {x : ℝ} (hx : 0 ≤ x)
    {m : ℕ} (hm : 0 < m) :
    x ^ m / (m.factorial : ℝ) ≤
      (Real.exp 1 * x / m) ^ m := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * m) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hpi := Real.pi_gt_three
    have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hbase : 0 ≤ (m : ℝ) / Real.exp 1 := by positivity
  have hden : ((m : ℝ) / Real.exp 1) ^ m ≤ (m.factorial : ℝ) := by
    calc
      ((m : ℝ) / Real.exp 1) ^ m ≤
          Real.sqrt (2 * Real.pi * m) * ((m : ℝ) / Real.exp 1) ^ m :=
        le_mul_of_one_le_left (pow_nonneg hbase _) hsqrt
      _ ≤ (m.factorial : ℝ) := Stirling.le_factorial_stirling m
  calc
    x ^ m / (m.factorial : ℝ) ≤
        x ^ m / (((m : ℝ) / Real.exp 1) ^ m) :=
      div_le_div_of_nonneg_left (pow_nonneg hx _)
        (pow_pos (div_pos hmreal (Real.exp_pos 1)) _) hden
    _ = (Real.exp 1 * x / m) ^ m := by
      rw [← div_pow]
      congr 1
      field_simp

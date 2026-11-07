-- Prove2me | Theorems.Thm_e7_continuous_test_zero_of_polynomial_approx
-- name    : e7_continuous_test_zero_of_polynomial_approx
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T06:25:06.443321+00:00
-- url     : https://prove2.me/theorems/7fe572f1-5dd4-4f63-bec1-06e35e5922a4
-- title:
--   e7_continuous_test_zero_of_polynomial_approx
-- statement:
--   Automatically extracted helper theorem e7_continuous_test_zero_of_polynomial_approx from oversized parent candidate 36dfbb02f7259909607e9c7b2ea61d13c82bc7906f739bb3c20fee07b43f20d8.
-- source:
--   candidate-decomposition:e7f29b55-7342-4ff0-afdb-be23ceaf9cb9:36dfbb02f7259909607e9c7b2ea61d13c82bc7906f739bb3c20fee07b43f20d8

import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem
import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformEmbedding
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

theorem e7_continuous_test_zero_of_polynomial_approx
    (G φ : ℝ → ℝ)
    (hGint : IntegrableOn G (Set.Ioi (0 : ℝ)) volume)
    (hGzero : ∀ y : ℝ, 1 < y → G y = 0)
    (hpoly : ∀ p : Polynomial ℝ,
      IntegrableOn (fun y : ℝ => p.eval y * G y)
          (Set.Ioi (0 : ℝ)) volume ∧
        (∫ y, p.eval y * G y
          ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = 0)
    (hφint : IntegrableOn (fun y : ℝ => φ y * G y)
      (Set.Ioi (0 : ℝ)) volume)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ p : Polynomial ℝ, ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 →
        ‖φ y - p.eval y‖ ≤ ε) :
    (∫ y, φ y * G y ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = 0 := by sorry

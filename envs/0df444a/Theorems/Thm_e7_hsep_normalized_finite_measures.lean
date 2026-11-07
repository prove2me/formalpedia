-- Prove2me | Theorems.Thm_e7_hsep_normalized_finite_measures
-- name    : e7_hsep_normalized_finite_measures
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T06:25:08.8392+00:00
-- url     : https://prove2.me/theorems/2ba4f217-1b56-466d-8062-0bc2f803da54
-- title:
--   e7_hsep_normalized_finite_measures
-- statement:
--   Automatically extracted helper theorem e7_hsep_normalized_finite_measures from oversized parent candidate 36dfbb02f7259909607e9c7b2ea61d13c82bc7906f739bb3c20fee07b43f20d8.
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

theorem e7_hsep_normalized_finite_measures
    {E V : Type*} [MeasurableSpace E] [Nonempty E]
    [FunLike V E ℝ] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Submodule ℝ V)
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ →
      IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ν₁) =
        ∫ x, (f.val : E → ℝ) x ∂ν₂) → ν₁ = ν₂)
    (μ ν : MeasureTheory.FiniteMeasure E)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hmass : μ.mass = ν.mass)
    (hraw : ∀ f : L,
      (∫ x, (f.val : E → ℝ) x ∂μ.toMeasure) =
        ∫ x, (f.val : E → ℝ) x ∂ν.toMeasure) :
    μ.toMeasure = ν.toMeasure := by sorry

-- Prove2me | Theorems.Thm_e7_finite_interval_exp_ibp
-- name    : e7_finite_interval_exp_ibp
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T06:54:21.36271+00:00
-- url     : https://prove2.me/theorems/e5c9f7b2-f0d4-4bb9-a356-2c52ccb54348
-- title:
--   e7_finite_interval_exp_ibp
-- statement:
--   Automatically extracted helper theorem e7_finite_interval_exp_ibp from oversized parent candidate dcd953a23f725a070ac191cef4ddb58557fddc058de13b87b62b5edcb2f71a48.
-- source:
--   candidate-decomposition:e7f29b55-7342-4ff0-afdb-be23ceaf9cb9:dcd953a23f725a070ac191cef4ddb58557fddc058de13b87b62b5edcb2f71a48

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

theorem e7_finite_interval_exp_ibp
    (T rate : ℝ) (qf qg : ℝ → ℝ)
    (hqf_cont : ContinuousOn qf (Set.uIcc 0 T))
    (hqf_deriv : ∀ t, t ∈ Set.Ioo (min 0 T) (max 0 T) →
      HasDerivAt qf (qg t) t)
    (hqg_int : IntervalIntegrable qg volume 0 T)
    (hexp_deriv_int : IntervalIntegrable
      (fun t => (-rate) * Real.exp (-rate * t)) volume 0 T) :
    (∫ t in (0 : ℝ)..T,
      qg t * Real.exp (-rate * t) +
        qf t * ((-rate) * Real.exp (-rate * t))) =
      Real.exp (-rate * T) * qf T - qf 0 := by sorry

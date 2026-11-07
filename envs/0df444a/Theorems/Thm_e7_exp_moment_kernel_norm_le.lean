-- Prove2me | Theorems.Thm_e7_exp_moment_kernel_norm_le
-- name    : e7_exp_moment_kernel_norm_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T07:13:40.89623+00:00
-- url     : https://prove2.me/theorems/42c088f7-2883-4229-856a-25a2ca13b581
-- title:
--   e7_exp_moment_kernel_norm_le
-- statement:
--   Automatically extracted helper theorem e7_exp_moment_kernel_norm_le from oversized parent candidate d2db63e11137724e20a853341a1bdaf5fcb4948fbdc6225faa463eef688991cc.
-- source:
--   candidate-decomposition:e7f29b55-7342-4ff0-afdb-be23ceaf9cb9:d2db63e11137724e20a853341a1bdaf5fcb4948fbdc6225faa463eef688991cc

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
import Definitions.Def_e7_exp_moment_kernel
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

theorem e7_exp_moment_kernel_norm_le
    (d : ℝ → ℝ) (k : ℕ) (B : ℝ)
    (hd_bound : ∀ r : ℝ, ‖d r‖ ≤ B)
    {y : ℝ} (hy : y ∈ Set.Ioc (0 : ℝ) 1) :
    ‖e7_exp_moment_kernel d k y‖ ≤ B := by sorry

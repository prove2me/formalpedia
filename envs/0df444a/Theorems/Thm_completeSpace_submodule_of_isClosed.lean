-- Prove2me | Theorems.Thm_completeSpace_submodule_of_isClosed
-- name    : completeSpace_submodule_of_isClosed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:24:59.504248+00:00
-- url     : https://prove2.me/theorems/aba2ad18-3f6f-4f00-b1b6-b824d5fa89a7
-- title:
--   completeSpace_submodule_of_isClosed
-- statement:
--   Automatically extracted helper theorem completeSpace_submodule_of_isClosed from oversized parent candidate 36dfbb02f7259909607e9c7b2ea61d13c82bc7906f739bb3c20fee07b43f20d8.
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

theorem completeSpace_submodule_of_isClosed
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (L : Submodule ℝ U) (hclosed : IsClosed (L : Set U)) : CompleteSpace L := by sorry

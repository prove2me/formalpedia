-- Prove2me | Theorems.Thm_e7IndicatorUBF_measurable
-- name    : e7IndicatorUBF_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T07:13:33.741303+00:00
-- url     : https://prove2.me/theorems/67114c90-4910-4f84-a0a4-5248d70e1e2e
-- title:
--   e7IndicatorUBF_measurable
-- statement:
--   Automatically extracted helper theorem e7IndicatorUBF_measurable from oversized parent candidate d2db63e11137724e20a853341a1bdaf5fcb4948fbdc6225faa463eef688991cc.
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
import Definitions.Def_e7IndicatorUBF
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

theorem e7IndicatorUBF_measurable {E : Type*} [MeasurableSpace E]
    (s : Set E) (hs : MeasurableSet s) :
    Measurable (e7IndicatorUBF s : E → ℝ) := by sorry

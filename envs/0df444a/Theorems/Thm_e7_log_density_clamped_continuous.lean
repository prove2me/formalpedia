-- Prove2me | Theorems.Thm_e7_log_density_clamped_continuous
-- name    : e7_log_density_clamped_continuous
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T11:40:34.146625+00:00
-- url     : https://prove2.me/theorems/af7b04f9-6f7d-4a7f-9e1e-a7391a7a768a
-- title:
--   e7_log_density_clamped_continuous
-- statement:
--   Automatically extracted helper theorem e7_log_density_clamped_continuous from oversized parent candidate 73804db67773f64e1cfa5f3fdec118acae00c374449fc9c40fdcb59e346c1322.
-- source:
--   candidate-decomposition:e7f29b55-7342-4ff0-afdb-be23ceaf9cb9:73804db67773f64e1cfa5f3fdec118acae00c374449fc9c40fdcb59e346c1322

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
import Definitions.Def_e7_clampIcc
import Definitions.Def_e7_log_density_clamped
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

theorem e7_log_density_clamped_continuous
    (d : ℝ → ℝ) (hd : Continuous d) (a b : ℝ) (hab : a ≤ b) (ha : 0 < a) :
    Continuous (e7_log_density_clamped d a b hab) := by sorry

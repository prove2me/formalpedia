-- Prove2me | Theorems.Thm_closure_range_of_dense_codRestrict
-- name    : closure_range_of_dense_codRestrict
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T06:54:19.080267+00:00
-- url     : https://prove2.me/theorems/a5c99812-d742-434a-a914-33f6db219b95
-- title:
--   closure_range_of_dense_codRestrict
-- statement:
--   Automatically extracted helper theorem closure_range_of_dense_codRestrict from oversized parent candidate dcd953a23f725a070ac191cef4ddb58557fddc058de13b87b62b5edcb2f71a48.
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

theorem closure_range_of_dense_codRestrict
    {D U : Type*} [AddCommMonoid D] [Module ℝ D]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (L : Submodule ℝ U) (f : D →ₗ[ℝ] U)
    (hmem : ∀ x, f x ∈ L)
    (hclosed : IsClosed (L : Set U))
    (hdense : DenseRange (LinearMap.codRestrict L f hmem)) :
    closure (Set.range f) = (L : Set U) := by sorry

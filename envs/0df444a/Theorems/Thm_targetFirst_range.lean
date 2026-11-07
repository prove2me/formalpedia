-- Prove2me | Theorems.Thm_targetFirst_range
-- name    : targetFirst_range
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T06:54:51.209481+00:00
-- url     : https://prove2.me/theorems/4fa46775-a8b3-4bd6-a9b4-90f797a44899
-- title:
--   targetFirst_range
-- statement:
--   Automatically extracted helper theorem targetFirst_range from oversized parent candidate dcd953a23f725a070ac191cef4ddb58557fddc058de13b87b62b5edcb2f71a48.
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
import Definitions.Def_targetFirstRaw
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

section TargetMaps
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
theorem targetFirst_range (A' : Submodule ℝ (U × U)) :
    Set.range (targetFirstRaw A') =
      (fun fg : U × U => fg.1) '' (A' : Set (U × U)) := by sorry
end TargetMaps

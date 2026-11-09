-- Prove2me | Theorems.Thm_e7_dense_lipschitz_functional_zero
-- name    : e7_dense_lipschitz_functional_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:54:21.008204+00:00
-- url     : https://prove2.me/theorems/c311839e-fa92-45e5-b533-3f39ab7c0625
-- title:
--   e7_dense_lipschitz_functional_zero
-- statement:
--   Automatically extracted helper theorem e7_dense_lipschitz_functional_zero from oversized parent candidate dcd953a23f725a070ac191cef4ddb58557fddc058de13b87b62b5edcb2f71a48.
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

theorem e7_dense_lipschitz_functional_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Submodule ℝ V) (S : Set V) (F : V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (happrox : ∀ x : L, ∀ ε : ℝ, 0 < ε →
      ∃ y, y ∈ S ∧ ‖(x : V) - y‖ < ε)
    (hLip : ∀ x y, ‖F x - F y‖ ≤ C * ‖x - y‖)
    (hzero : ∀ y, y ∈ S → F y = 0) :
    ∀ x : L, F x = 0 := by sorry

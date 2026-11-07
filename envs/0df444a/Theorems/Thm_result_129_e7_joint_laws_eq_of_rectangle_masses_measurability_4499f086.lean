-- Prove2me | Theorems.Thm_result_129_e7_joint_laws_eq_of_rectangle_masses_measurability_4499f086
-- name    : result_129_e7_joint_laws_eq_of_rectangle_masses_measurability_4499f086
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T11:55:26.765545+00:00
-- url     : https://prove2.me/theorems/70f9a351-692d-42c9-83c1-f547e1e3392d
-- title:
--   129 e7 joint laws eq of rectangle masses: Measurability
-- statement:
--   The specified function or random variable is measurable under the theorem's hypotheses.

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

theorem result_129_e7_joint_laws_eq_of_rectangle_masses_measurability_4499f086
    {ι E Ω Ω' : Type*} [Fintype ι] [MeasurableSpace E]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (x : Ω → ι → E) (y : Ω' → ι → E)
    (hx : Measurable x) (hy : Measurable y)
    (hrect : ∀ B : ι → Set E, (∀ i, MeasurableSet (B i)) →
      P {ω | ∀ i, x ω i ∈ B i} = Q {ω | ∀ i, y ω i ∈ B i}) 
    (hpi : (let rect : (ι → Set E) → Set (ι → E) := (fun B => {z | ∀ i, z i ∈ B i}); let S : Set (Set (ι → E)) := ( {s | ∃ B, (∀ i, MeasurableSet (B i)) ∧ s = rect B}); IsPiSystem S))
    (hSmeas : (let rect : (ι → Set E) → Set (ι → E) := (fun B => {z | ∀ i, z i ∈ B i}); let S : Set (Set (ι → E)) := ( {s | ∃ B, (∀ i, MeasurableSet (B i)) ∧ s = rect B}); ∀ s, s ∈ S → MeasurableSet s))
    : (let rect : (ι → Set E) → Set (ι → E) := (fun B => {z | ∀ i, z i ∈ B i}); let S : Set (Set (ι → E)) := ( {s | ∃ B, (∀ i, MeasurableSet (B i)) ∧ s = rect B}); (inferInstance : MeasurableSpace (ι → E)) =
      MeasurableSpace.generateFrom S) := by sorry

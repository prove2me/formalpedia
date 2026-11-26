-- Prove2me | solution 1 for ReweightedNPMLE.continuous_gaussianSquaredLogRatioGap
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:08:52.439194+00:00
-- url     : https://prove2.me/submissions/f138f223-d475-416f-ab83-62ae84329df9

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_CompactOptimizerEvents
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianJointEvents
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SmallSupportProbability
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_continuous_gaussian_probabilityMixtureValue_joint
import Theorems.Thm_ReweightedNPMLE_gaussian_probabilityMixtureValue_pos

/-!
# Joint Borel events for Gaussian optimizer laws

All events concern the full probability-law optimizer space. Compact law
projection proves measurability of nonuniqueness, support failure, and
ordinary likelihood and fitted-log failures jointly in data and weights.
-/

open Set MeasureTheory
open scoped Topology BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (gaussianSquaredLogRatioGap (n := n) θ) := by
  let F := fun p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦
    probabilityMixtureValue (fun a j ↦ gaussianKernel d (p.1.1 j) (θ a)) p.2.1
  let F₀ := fun p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦
    probabilityMixtureValue (fun a j ↦ gaussianKernel d (p.1.1 j) (θ a)) p.2.2
  have hm := continuous_gaussian_probabilityMixtureValue_joint (n := n) θ hθ
  have hmap : Continuous (fun p : GaussianDataWeight d n ×
      (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦ (p.1.1, p.2.1)) :=
    (continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)
  have hmap₀ : Continuous (fun p : GaussianDataWeight d n ×
      (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦ (p.1.1, p.2.2)) :=
    (continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)
  have hF : Continuous F := hm.comp hmap
  have hF₀ : Continuous F₀ := hm.comp hmap₀
  change Continuous (fun p ↦ ∑ i, (Real.log (F p i / F₀ p i)) ^ 2)
  apply continuous_finsetSum
  intro i _
  have hfi := (continuous_apply i).comp hF
  have hf₀i := (continuous_apply i).comp hF₀
  have hpos (p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) :
      0 < F p i := gaussian_probabilityMixtureValue_pos p.1.1 θ hθ p.2.1 i
  have hpos₀ (p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) :
      0 < F₀ p i := gaussian_probabilityMixtureValue_pos p.1.1 θ hθ p.2.2 i
  exact ((hfi.div hf₀i (fun p ↦ (hpos₀ p).ne')).log
    (fun p ↦ (div_pos (hpos p) (hpos₀ p)).ne')).pow 2

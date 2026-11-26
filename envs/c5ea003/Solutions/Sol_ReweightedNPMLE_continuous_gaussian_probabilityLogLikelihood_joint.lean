-- Prove2me | solution 1 for ReweightedNPMLE.continuous_gaussian_probabilityLogLikelihood_joint
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:08:54.966819+00:00
-- url     : https://prove2.me/submissions/3b5a3db5-af49-418c-a0f8-aa0bbe38b998

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
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
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
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_continuous_gaussian_probabilityMixtureValue_joint
import Theorems.Thm_ReweightedNPMLE_gaussian_probabilityMixtureValue_pos

/-!
# Joint continuity of compact-parameter probability integrals

Weak convergence of the law and uniform convergence of the integrand can
vary simultaneously. The probability normalization bounds the integral of
the varying integrand difference by its supremum norm.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
      weightedLogLikelihood p.1.2
        (probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1.1 i) (θ a)) p.2)) := by
  let M := fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
    probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1.1 i) (θ a)) p.2
  have hmap : Continuous (fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
      (p.1.1, p.2)) := (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hM : Continuous M :=
    (continuous_gaussian_probabilityMixtureValue_joint θ hθ).comp hmap
  change Continuous (fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
    ∑ i, p.1.2 i * Real.log (M p i))
  apply continuous_finsetSum
  intro i _
  have hw : Continuous (fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
      p.1.2 i) := (continuous_apply i).comp (continuous_snd.comp continuous_fst)
  have hf : Continuous (fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
      M p i) := (continuous_apply i).comp hM
  exact hw.mul (hf.log (fun p ↦ (gaussian_probabilityMixtureValue_pos p.1.1 θ hθ p.2 i).ne'))

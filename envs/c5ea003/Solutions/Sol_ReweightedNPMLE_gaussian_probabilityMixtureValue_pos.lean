-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_probabilityMixtureValue_pos
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:08:11.356272+00:00
-- url     : https://prove2.me/submissions/ed9079d3-c168-46ed-8f0d-a9fede591773

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

-- Inline helpers preserved from ReweightedNPMLE.ProbabilityOptimizerFiber.
section
/-!
# Optimizer fibers over arbitrary probability measures

These are genuine probability-measure fibers, not finite coefficient fibers.
Continuous moment constraints are closed for weak convergence and the fiber
is compact on a compact parameter space. The likelihood contact identity
holds almost everywhere and everywhere on the topological support of every
optimizing measure, including measures with infinite support.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE





















theorem probabilityMixtureValue_eq_integral {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (μ : ProbabilityMeasure Θ) :
    probabilityMixtureValue A μ = ∫ θ, A θ ∂μ := by
  have hi := hA.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace A)
    (μ := (μ : Measure Θ))
  funext i
  exact (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).integral_comp_comm hi

theorem probabilityMixtureValue_mem_convexHull {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (μ : ProbabilityMeasure Θ) :
    probabilityMixtureValue A μ ∈ convexHull ℝ (range A) := by
  rw [probabilityMixtureValue_eq_integral A hA μ]
  exact (convex_convexHull ℝ (range A)).integral_mem
    (isCompact_convexHull_of_isCompact (isCompact_range hA)).isClosed
    (Eventually.of_forall fun θ ↦ subset_convexHull ℝ _ (mem_range_self θ))
    (hA.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace A))













end ReweightedNPMLE
end

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
    {d n : ℕ} (x : Fin n → Point d) (θ : Θ → Point d) (hθ : Continuous θ)
    (μ : ProbabilityMeasure Θ) (i : Fin n) :
    0 < probabilityMixtureValue (fun a j ↦ gaussianKernel d (x j) (θ a)) μ i := by
  let A := fun a j ↦ gaussianKernel d (x j) (θ a)
  have hA : Continuous A := by
    apply continuous_pi
    intro j
    have hpair : Continuous (fun a : Θ ↦ (x j, θ a)) := continuous_const.prodMk hθ
    have hh : Continuous ((fun p : Point d × Point d ↦ gaussianKernel d p.1 p.2) ∘
        (fun a : Θ ↦ (x j, θ a))) := (continuous_gaussianKernel d).comp hpair
    exact hh
  have hCpos : convexHull ℝ (range A) ⊆ positiveVectors n :=
    convexHull_min (by rintro a ⟨b, rfl⟩; exact fun j ↦ gaussianKernel_pos d (x j) (θ b))
      (convex_positiveVectors n)
  exact hCpos (probabilityMixtureValue_mem_convexHull A hA μ) i

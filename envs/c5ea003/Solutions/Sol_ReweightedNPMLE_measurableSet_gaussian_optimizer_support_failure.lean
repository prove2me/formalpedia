-- Prove2me | solution 1 for ReweightedNPMLE.measurableSet_gaussian_optimizer_support_failure
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:16:27.613805+00:00
-- url     : https://prove2.me/submissions/890d6a40-17bd-4839-a41b-6dfe7a2cc142

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
import Theorems.Thm_ReweightedNPMLE_continuous_gaussian_probabilityLogLikelihood_joint
import Theorems.Thm_ReweightedNPMLE_measurableSet_exists_compactOptimizer_outside_closed
import Theorems.Thm_ReweightedNPMLE_mem_smallSupportProbabilityLaws_iff
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureValue_finiteProbabilityMeasure

-- Inline helpers preserved from ReweightedNPMLE.FiniteOptimizerFiber.
section
/-!
# Extreme finite mixture fibers

This file isolates the finite-dimensional core of the paper's optimizer-fiber
lemma.  A probability vector represents a finite mixing law.  If the
dictionary vectors indexed by its nonzero masses are linearly independent,
then that representation is an extreme point of the fiber of all probability
vectors with the same fitted value.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE



theorem finiteSimplex_eq_stdSimplex (m : ℕ) :
    finiteSimplex m = stdSimplex ℝ (Fin m) := rfl

theorem isCompact_finiteSimplex (m : ℕ) : IsCompact (finiteSimplex m) := by
  rw [finiteSimplex_eq_stdSimplex]
  exact isCompact_stdSimplex ℝ (Fin m)













































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.FiniteProbabilityExtreme.
section
/-!
# Independent finite mixing laws are full-fiber extreme points

Finite-support representation and uniqueness are proved for arbitrary
probability measures concentrated on that finite support. Consequently,
an independent finite mixing law is extreme against decompositions into
arbitrary probability measures, not only against finite coefficient vectors.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE













theorem probabilityIntegralFunctional_finiteProbabilityMeasure {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {m : ℕ} (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (f : C(Θ, ℝ)) :
    probabilityIntegralFunctional (finiteProbabilityMeasure θ p hp) f = ∑ j, p j * f (θ j) := by
  have hh := congrFun (probabilityMixtureValue_finiteProbabilityMeasure
    (fun x : Θ ↦ fun _ : Fin 1 ↦ f x) (by fun_prop) θ p hp) (0 : Fin 1)
  simpa only [probabilityMixtureValue, probabilityIntegralFunctional, finiteMixtureValue,
    Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh













end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.SmallSupportProbability.
section
/-!
# Closed sets of probability laws with bounded finite support

The at-most-`m`-atom laws form a compact set in the weak topology. Finite
atomic laws are parameterized by compact atom lists and closed simplices,
including zero masses and coincident locations.
-/

open Set MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE



theorem continuous_finiteProbabilityLawMap {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (m : ℕ) : Continuous (finiteProbabilityLawMap (Θ := Θ) m) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  change Continuous (fun p : (Fin m → Θ) × (finiteSimplex m) ↦
    probabilityIntegralFunctional (finiteProbabilityMeasure p.1 p.2.val p.2.property) f)
  simp_rw [probabilityIntegralFunctional_finiteProbabilityMeasure]
  apply continuous_finsetSum
  intro j _
  have hp : Continuous (fun p : (Fin m → Θ) × (finiteSimplex m) ↦ p.2.val j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
  have hθ : Continuous (fun p : (Fin m → Θ) × (finiteSimplex m) ↦ p.1 j) :=
    (continuous_apply j).comp continuous_fst
  exact hp.mul (f.continuous.comp hθ)

theorem isCompact_range_finiteProbabilityLawMap {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (m : ℕ) : IsCompact (range (finiteProbabilityLawMap (Θ := Θ) m)) := by
  letI : CompactSpace (finiteSimplex m) := isCompact_iff_compactSpace.mp (isCompact_finiteSimplex m)
  exact isCompact_range (continuous_finiteProbabilityLawMap m)



theorem isCompact_smallSupportProbabilityLaws {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (m : ℕ) : IsCompact (smallSupportProbabilityLaws Θ m) :=
  isCompact_iUnion (fun k ↦ isCompact_range_finiteProbabilityLawMap (k : ℕ))



theorem isClosed_smallSupportProbabilityLaws {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (m : ℕ) : IsClosed (smallSupportProbabilityLaws Θ m) :=
  (isCompact_smallSupportProbabilityLaws m).isClosed

end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianJointEvents.
section
/-!
# Joint Borel events for Gaussian optimizer laws

All events concern the full probability-law optimizer space. Compact law
projection proves measurability of nonuniqueness, support failure, and
ordinary likelihood and fitted-log failures jointly in data and weights.
-/

open Set MeasureTheory
open scoped Topology BigOperators

namespace ReweightedNPMLE







theorem continuous_gaussianProbabilityLogLikelihood {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (gaussianProbabilityLogLikelihood (n := n) θ) :=
  continuous_gaussian_probabilityLogLikelihood_joint θ hθ



























end ReweightedNPMLE
end

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
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) {R : ℝ} (hR : 0 ≤ R) :
    MeasurableSet {p : GaussianDataWeight d n | ∃ μ : ProbabilityMeasure Θ,
      μ ∈ gaussianProbabilityOptimizerSet θ p ∧
        ¬((μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R)} := by
  letI : MetricSpace (ProbabilityMeasure Θ) := TopologicalSpace.metrizableSpaceMetric _
  have heq : {p : GaussianDataWeight d n | ∃ μ : ProbabilityMeasure Θ,
      μ ∈ gaussianProbabilityOptimizerSet θ p ∧
        ¬((μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R)} =
      {p | ∃ μ : ProbabilityMeasure Θ, (p, μ) ∈ compactOptimizerGraph
        (gaussianProbabilityLogLikelihood θ) ∧ μ ∉ smallSupportProbabilityLaws Θ (Nat.floor R)} := by
    ext p
    simp only [mem_setOf_eq, mem_smallSupportProbabilityLaws_iff, Nat.le_floor_iff hR]
    rfl
  rw [heq]
  exact measurableSet_exists_compactOptimizer_outside_closed _
    (continuous_gaussianProbabilityLogLikelihood θ hθ) _ (isClosed_smallSupportProbabilityLaws _)

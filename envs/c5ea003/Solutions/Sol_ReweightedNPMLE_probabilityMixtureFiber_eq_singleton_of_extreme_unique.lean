-- Prove2me | solution 1 for ReweightedNPMLE.probabilityMixtureFiber_eq_singleton_of_extreme_unique
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:14:43.133539+00:00
-- url     : https://prove2.me/submissions/b8c81e00-8929-4de1-a86a-ca44f3289dfb

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_nonempty_of_mem_convexHull

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







theorem probabilityMixtureValue_convexCombination {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (a b : ℝ≥0) (hab : a + b = 1) (μ ν : ProbabilityMeasure Θ) :
    probabilityMixtureValue A (probabilityConvexCombination a b hab μ ν) =
      (a : ℝ) • probabilityMixtureValue A μ + (b : ℝ) • probabilityMixtureValue A ν := by
  funext i
  have hμi := ((continuous_apply i).comp hA).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := (μ : Measure Θ))
  have hνi := ((continuous_apply i).comp hA).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := (ν : Measure Θ))
  change Integrable (fun θ ↦ A θ i) (μ : Measure Θ) at hμi
  change Integrable (fun θ ↦ A θ i) (ν : Measure Θ) at hνi
  change (∫ θ, A θ i ∂(a • (μ : Measure Θ) + b • (ν : Measure Θ))) = _
  rw [integral_add_measure hμi.smul_measure_nnreal hνi.smul_measure_nnreal]
  simp only [integral_smul_nnreal_measure, probabilityMixtureValue, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rfl

theorem probabilityMixtureFiber_convexCombination {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (a b : ℝ≥0) (hab : a + b = 1) (μ ν : ProbabilityMeasure Θ)
    (hμ : μ ∈ probabilityMixtureFiber A v) (hν : ν ∈ probabilityMixtureFiber A v) :
    probabilityConvexCombination a b hab μ ν ∈ probabilityMixtureFiber A v := by
  change probabilityMixtureValue A (probabilityConvexCombination a b hab μ ν) = v
  rw [probabilityMixtureValue_convexCombination A hA a b hab μ ν,
    show probabilityMixtureValue A μ = v from hμ, show probabilityMixtureValue A ν = v from hν,
    ← add_smul]
  have hh : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast hab
  rw [hh, one_smul]







theorem continuous_probabilityMixtureValue {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) :
    Continuous (probabilityMixtureValue A) := by
  apply continuous_pi
  intro i
  exact ProbabilityMeasure.continuous_integral_continuousMap
    (⟨fun θ ↦ A θ i, (continuous_apply i).comp hA⟩ : C(Θ, ℝ))

theorem isCompact_probabilityMixtureFiber {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ) :
    IsCompact (probabilityMixtureFiber A v) := by
  exact (isClosed_eq (continuous_probabilityMixtureValue A hA) continuous_const).isCompact

















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.ProbabilityFiberGeometry.
section
/-!
# Real-vector-space geometry of full probability fibers

Integration against continuous test functions embeds probability measures
injectively into a locally convex real vector space with its product topology.
The weakly compact mixture fiber has a compact convex image. Extreme points
are thus mathlib extreme points of a faithful representation of the full
probability-measure fiber, rather than of a finite coefficient simplex.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE



theorem continuous_probabilityIntegralFunctional {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ] :
    Continuous (probabilityIntegralFunctional (Θ := Θ)) := by
  apply continuous_pi
  intro f
  exact ProbabilityMeasure.continuous_integral_continuousMap f

theorem probabilityIntegralFunctional_injective {Θ : Type*}
    [TopologicalSpace Θ] [HasOuterApproxClosed Θ] [MeasurableSpace Θ] [BorelSpace Θ] :
    Function.Injective (probabilityIntegralFunctional (Θ := Θ)) := by
  intro μ ν h
  have hh : μ.toFiniteMeasure = ν.toFiniteMeasure :=
    FiniteMeasure.ext_of_forall_integral_eq (fun f ↦ congrFun h f.toContinuousMap)
  apply ProbabilityMeasure.toMeasure_injective
  exact congrArg (fun ρ : FiniteMeasure Θ ↦ (ρ : Measure Θ)) hh

theorem probabilityIntegralFunctional_convexCombination {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (a b : ℝ≥0) (hab : a + b = 1) (μ ν : ProbabilityMeasure Θ) :
    probabilityIntegralFunctional (probabilityConvexCombination a b hab μ ν) =
      (a : ℝ) • probabilityIntegralFunctional μ + (b : ℝ) • probabilityIntegralFunctional ν := by
  funext f
  have hμ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    (μ := (μ : Measure Θ))
  have hν := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    (μ := (ν : Measure Θ))
  change (∫ θ, f θ ∂(a • (μ : Measure Θ) + b • (ν : Measure Θ))) = _
  rw [integral_add_measure hμ.smul_measure_nnreal hν.smul_measure_nnreal]
  simp only [integral_smul_nnreal_measure, probabilityIntegralFunctional, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rfl



theorem isCompact_probabilityFiberImage {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ) :
    IsCompact (probabilityFiberImage A v) :=
  (isCompact_probabilityMixtureFiber A hA v).image continuous_probabilityIntegralFunctional

theorem convex_probabilityFiberImage {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ) :
    Convex ℝ (probabilityFiberImage A v) := by
  rintro x ⟨μ, hμ, rfl⟩ y ⟨ν, hν, rfl⟩ a b ha hb hab
  let a' : ℝ≥0 := ⟨a, ha⟩
  let b' : ℝ≥0 := ⟨b, hb⟩
  have hab' : a' + b' = 1 := by apply Subtype.ext; exact hab
  refine ⟨probabilityConvexCombination a' b' hab' μ ν,
    probabilityMixtureFiber_convexCombination A hA v a' b' hab' μ ν hμ hν, ?_⟩
  exact probabilityIntegralFunctional_convexCombination a' b' hab' μ ν



theorem isExtremeProbabilityMixture_mem_fiber {Θ : Type*}
    [TopologicalSpace Θ] [HasOuterApproxClosed Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) (μ : ProbabilityMeasure Θ)
    (hμ : IsExtremeProbabilityMixture A v μ) : μ ∈ probabilityMixtureFiber A v := by
  obtain ⟨ν, hν, heq⟩ := hμ.1
  exact probabilityIntegralFunctional_injective heq ▸ hν



theorem probabilityMixtureFiber_extreme_nonempty {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (hv : v ∈ convexHull ℝ (range A)) :
    ∃ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A v μ := by
  have hnonempty : (probabilityFiberImage A v).Nonempty :=
    (probabilityMixtureFiber_nonempty_of_mem_convexHull A hA v hv).image _
  obtain ⟨x, hx⟩ := (isCompact_probabilityFiberImage A hA v).extremePoints_nonempty hnonempty
  obtain ⟨μ, hμ, rfl⟩ := hx.1
  exact ⟨μ, hx⟩

theorem probabilityFiberImage_kreinMilman {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ) :
    closure (convexHull ℝ ((probabilityFiberImage A v).extremePoints ℝ)) =
      probabilityFiberImage A v :=
  closure_convexHull_extremePoints (isCompact_probabilityFiberImage A hA v)
    (convex_probabilityFiberImage A hA v)



end ReweightedNPMLE
end

/-!
# Real-vector-space geometry of full probability fibers

Integration against continuous test functions embeds probability measures
injectively into a locally convex real vector space with its product topology.
The weakly compact mixture fiber has a compact convex image. Extreme points
are thus mathlib extreme points of a faithful representation of the full
probability-measure fiber, rather than of a finite coefficient simplex.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The full probability-measure uniqueness step of Krein--Milman. No
finite-dictionary or finite-support assumption is made here. -/
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (hv : v ∈ convexHull ℝ (range A))
    (hunique : ∀ μ ν : ProbabilityMeasure Θ,
      IsExtremeProbabilityMixture A v μ → IsExtremeProbabilityMixture A v ν → μ = ν) :
    ∃ μ : ProbabilityMeasure Θ, probabilityMixtureFiber A v = {μ} ∧
      IsExtremeProbabilityMixture A v μ := by
  obtain ⟨μ, hμ⟩ := probabilityMixtureFiber_extreme_nonempty A hA v hv
  have hext : (probabilityFiberImage A v).extremePoints ℝ = {probabilityIntegralFunctional μ} := by
    ext x
    constructor
    · intro hx
      obtain ⟨ν, hν, rfl⟩ := hx.1
      exact congrArg probabilityIntegralFunctional (hunique ν μ hx hμ)
    · rintro rfl
      exact hμ
  have himage : probabilityFiberImage A v = {probabilityIntegralFunctional μ} := by
    rw [← probabilityFiberImage_kreinMilman A hA v, hext, convexHull_singleton, closure_singleton]
  refine ⟨μ, ?_, hμ⟩
  ext ν
  constructor
  · intro hν
    have hh : probabilityIntegralFunctional ν ∈ probabilityFiberImage A v := ⟨ν, hν, rfl⟩
    rw [himage] at hh
    exact probabilityIntegralFunctional_injective hh
  · intro hν
    have heq : ν = μ := hν
    rw [heq]
    exact isExtremeProbabilityMixture_mem_fiber A v μ hμ

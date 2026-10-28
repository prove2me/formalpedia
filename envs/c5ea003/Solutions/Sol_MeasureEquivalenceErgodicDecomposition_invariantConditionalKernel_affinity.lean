-- Prove2me | solution 1 for MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_affinity
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:25:59.287992+00:00
-- url     : https://prove2.me/submissions/3b0263dd-5c2a-40ec-b585-fc1140aaa5c3

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_HellingerKernel
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Tactic
import Theorems.Thm_MeasureEquivalenceHellinger_affinity_compProd
import Theorems.Thm_MeasureEquivalenceHellinger_affinity_map_leftInverse

set_option autoImplicit false

namespace MeasurableEquiv
end MeasurableEquiv
namespace MeasureEquivalenceCompactAveraging
end MeasureEquivalenceCompactAveraging
namespace MeasureEquivalenceDenseInvariance
end MeasureEquivalenceDenseInvariance
namespace MeasureEquivalenceDensity
end MeasureEquivalenceDensity
namespace MeasureEquivalenceDensityGraph
end MeasureEquivalenceDensityGraph
namespace MeasureEquivalenceEquidecomposition
end MeasureEquivalenceEquidecomposition
namespace MeasureEquivalenceEquidecomposition.greedyRemainder
end MeasureEquivalenceEquidecomposition.greedyRemainder
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
namespace MeasureEquivalenceInducedCorners
end MeasureEquivalenceInducedCorners
namespace MeasureEquivalenceInvariantGraph
end MeasureEquivalenceInvariantGraph
namespace MeasureEquivalenceInverseAC
end MeasureEquivalenceInverseAC
namespace MeasureEquivalenceL2Coefficients
end MeasureEquivalenceL2Coefficients
namespace MeasureEquivalenceL2Restriction
end MeasureEquivalenceL2Restriction
namespace MeasureEquivalenceL2Transport
end MeasureEquivalenceL2Transport
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
namespace MeasureEquivalenceMarkov.kernelIterate
end MeasureEquivalenceMarkov.kernelIterate
namespace MeasureEquivalenceRNGraph
end MeasureEquivalenceRNGraph
namespace MeasureEquivalenceRNPresentation
end MeasureEquivalenceRNPresentation
namespace MeasureEquivalenceResearch
end MeasureEquivalenceResearch
namespace MeasureEquivalenceRestrictedPhase
end MeasureEquivalenceRestrictedPhase
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages
end MeasureEquivalenceRestrictedProduct.CompatibleStages
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
end MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
namespace MeasureEquivalenceRestrictedRoots
end MeasureEquivalenceRestrictedRoots
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
namespace MeasureEquivalenceRootContinuity
end MeasureEquivalenceRootContinuity
namespace MeasureEquivalenceSharedDensity
end MeasureEquivalenceSharedDensity
namespace MeasureEquivalenceSolenoid
end MeasureEquivalenceSolenoid
namespace MeasureEquivalenceTopology
end MeasureEquivalenceTopology
namespace MeasureEquivalenceZeroSumAffinity
end MeasureEquivalenceZeroSumAffinity
namespace MeasureUnitary
end MeasureUnitary
namespace MeasureUnitary.FiniteBorelSection
end MeasureUnitary.FiniteBorelSection
namespace OperatorCoding
end OperatorCoding
namespace OperatorCoding.operatorUnitaryPair
end OperatorCoding.operatorUnitaryPair
namespace lp
end lp

-- Preserved source skeleton: HellingerKernel
section
/-! Actual disintegration of Hellinger affinity for equal-marginal kernels. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (μ : Measure X) [IsFiniteMeasure μ]
    (κ η : Kernel X Y) [IsFiniteKernel κ] [IsFiniteKernel η]







theorem kernelAffinityIntegrand_measurable : Measurable (kernelAffinityIntegrand κ η) :=
  (κ.measurable_rnDeriv (κ+η)).ennreal_toReal.sqrt.mul
    (η.measurable_rnDeriv (κ+η)).ennreal_toReal.sqrt

theorem affinity_kernel_fiber (x : X) :
    (∫ y, kernelAffinityIntegrand κ η (x,y) ∂((κ+η) x)) = affinity (κ x) (η x) := by
  rw [affinity_integral]
  apply integral_congr_ae
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := κ+η) (a := x),
    η.rnDeriv_eq_rnDeriv_measure (η := κ+η) (a := x)] with y hk he
  simp only [kernelAffinityIntegrand, hk, he]
  rfl

theorem kernelAffinity_measurable : Measurable (fun x => affinity (κ x) (η x)) := by
  have h := (kernelAffinityIntegrand_measurable κ η).stronglyMeasurable.integral_kernel_prod_right'
    (κ := κ+η)
  have he : (fun x => ∫ y, kernelAffinityIntegrand κ η (x,y) ∂((κ+η) x)) =
      fun x => affinity (κ x) (η x) := funext (affinity_kernel_fiber κ η)
  rw [he] at h
  exact h.measurable



end MeasureEquivalenceHellinger

end

-- Preserved source skeleton: InvariantConditional
section
/-!
The exact invariant sigma-algebra and its actual conditional-probability
kernel. This module establishes invariance and reconstruction; it does
not assert ergodicity of the component probabilities.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace MeasureEquivalenceErgodicDecomposition



variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]











theorem invariantBaseMap_measurable : Measurable (invariantBaseMap (G := G) (Z := Z)) :=
  measurable_id'' (invariantSigma_le (G := G))



section Conditional

variable [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]





theorem invariantConditionalKernel_apply (z : Z) :
    invariantConditionalKernel (G := G) μ z = condExpKernel μ (invariantSigma (G := G)) z := rfl









theorem invariantBaseKernel_joint :
    (μ.map (invariantBaseMap (G := G))) ⊗ₘ invariantBaseKernel (G := G) μ =
      μ.map (fun z => (invariantBaseMap (G := G) z, z)) := by
  have h := compProd_trim_condExpKernel (μ := μ) (invariantSigma_le (G := G))
  rw [trim_eq_map] at h
  exact h











end Conditional

end MeasureEquivalenceErgodicDecomposition

end

-- Preserved source skeleton: InvariantAffinity
section
/-! Affinity disintegration over the actual invariant sigma algebra.
Exceptional sets may depend on the invariant event; no uncountable
intersection of conull sets is taken. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceErgodicDecomposition

open MeasureEquivalenceHellinger

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] [MeasurableSpace.CountablyGenerated Z]
    (μ : Measure Z) [IsFiniteMeasure μ]

theorem invariantBaseKernel_joint_map_of_ae_invariance (e : Z ≃ᵐ Z)
    (hinv : ∀ s : Set Z, MeasurableSet[invariantSigma (G := G)] s →
      e ⁻¹' s =ᵐ[μ] s) :
    (μ.map (invariantBaseMap (G := G))) ⊗ₘ
        (invariantBaseKernel (G := G) μ).map e =
      (μ.map e).map (fun z => (invariantBaseMap (G := G) z,z)) := by
  rw [Measure.compProd_map e.measurable, invariantBaseKernel_joint]
  have hgraph : Measurable (fun z : Z => (invariantBaseMap (G := G) z,z)) :=
    (invariantBaseMap_measurable (G := G)).prodMk measurable_id
  rw [Measure.map_map (measurable_id.prodMap e.measurable) hgraph,
    Measure.map_map hgraph e.measurable]
  change μ.map (fun z => (invariantBaseMap (G := G) z,e z)) =
    μ.map (fun z => (invariantBaseMap (G := G) (e z),e z))
  apply Measure.ext_prod
  intro B C hB hC
  have hp2 : Measurable (fun z : Z => (invariantBaseMap (G := G) (e z),e z)) :=
    ((invariantBaseMap_measurable (G := G)).comp e.measurable).prodMk e.measurable
  rw [Measure.map_apply ((invariantBaseMap_measurable (G := G)).prodMk e.measurable)
      (hB.prod hC),
    Measure.map_apply hp2 (hB.prod hC)]
  apply measure_congr
  have h := hinv (B : Set Z) hB
  rw [Filter.eventuallyEq_set] at h ⊢
  filter_upwards [h] with z hz
  change (z ∈ B ∧ e z ∈ C) ↔ (e z ∈ B ∧ e z ∈ C)
  change (e z ∈ B ↔ z ∈ B) at hz
  rw [hz]



end MeasureEquivalenceErgodicDecomposition

end

/-! Affinity disintegration over the actual invariant sigma algebra.
Exceptional sets may depend on the invariant event; no uncountable
intersection of conull sets is taken. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceHellinger
variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] [MeasurableSpace.CountablyGenerated Z]
    (μ : Measure Z) [IsFiniteMeasure μ]

theorem solution (e : Z ≃ᵐ Z)
    (hinv : ∀ s : Set Z, MeasurableSet[invariantSigma (G := G)] s →
      e ⁻¹' s =ᵐ[μ] s) :
    affinity μ (μ.map e) =
      ∫ x, affinity (invariantConditionalKernel (G := G) μ x)
        ((invariantConditionalKernel (G := G) μ x).map e) ∂μ := by
  let β := μ.map (invariantBaseMap (G := G))
  let κ := invariantBaseKernel (G := G) μ
  let j : Z → InvariantBase G Z × Z := fun z => (invariantBaseMap z,z)
  have hj : Measurable j :=
    (invariantBaseMap_measurable (G := G)).prodMk measurable_id
  have hleft : Function.LeftInverse Prod.snd j := fun _ => rfl
  calc
    affinity μ (μ.map e) = affinity (μ.map j) ((μ.map e).map j) :=
      (affinity_map_leftInverse j hj Prod.snd measurable_snd hleft μ (μ.map e)).symm
    _ = affinity (β ⊗ₘ κ) (β ⊗ₘ κ.map e) := by
      have h1 : β ⊗ₘ κ = μ.map j := invariantBaseKernel_joint μ
      have h2 : β ⊗ₘ κ.map e = (μ.map e).map j :=
        invariantBaseKernel_joint_map_of_ae_invariance μ e hinv
      simp only [h1, h2]
    _ = ∫ x, affinity (κ x) ((κ.map e) x) ∂β := affinity_compProd β κ (κ.map e)
    _ = ∫ x, affinity (κ (invariantBaseMap (G := G) x))
        ((κ.map e) (invariantBaseMap (G := G) x)) ∂μ :=
      integral_map (invariantBaseMap_measurable (G := G)).aemeasurable
        (kernelAffinity_measurable κ (κ.map e)).aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        simp only [κ, invariantBaseKernel, invariantBaseMap,
          invariantConditionalKernel_apply, Kernel.map_apply _ e.measurable]
        rfl)

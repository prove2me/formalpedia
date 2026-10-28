-- Prove2me | solution 1 for MeasureEquivalenceErgodicDecomposition.conditional_fiber_constant
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:19:56.607247+00:00
-- url     : https://prove2.me/submissions/fc9e8c15-3209-45d2-839c-0e7d3182906f

import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Tactic

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















theorem invariantBaseKernel_joint :
    (μ.map (invariantBaseMap (G := G))) ⊗ₘ invariantBaseKernel (G := G) μ =
      μ.map (fun z => (invariantBaseMap (G := G) z, z)) := by
  have h := compProd_trim_condExpKernel (μ := μ) (invariantSigma_le (G := G))
  rw [trim_eq_map] at h
  exact h











end Conditional

end MeasureEquivalenceErgodicDecomposition

end

/-! The actual invariant conditional kernel is constant almost everywhere
on almost every conditional fiber. Countability is used only for a family
that determines finite measures, so no AE/uncountable-forall swap is made. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]

theorem solution {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountablySeparated Y]
    (f : InvariantBase G Z → Y) (hf : Measurable f) :
    ∀ᵐ x ∂μ, ∀ᵐ z ∂(invariantConditionalKernel (G := G) μ x),
      f (invariantBaseMap (G := G) z) = f (invariantBaseMap (G := G) x) := by
  let β := μ.map (invariantBaseMap (G := G))
  let κ := invariantBaseKernel (G := G) μ
  have hj : (fun p : InvariantBase G Z × Z => f p.1) =ᵐ[β ⊗ₘ κ]
      (fun p => f (invariantBaseMap (G := G) p.2)) := by
    apply Filter.EventuallyEq.of_forall_separating_mem_iff MeasurableSet
    intro U hU
    have hp : MeasurableSet {p : InvariantBase G Z × Z |
        f p.1 ∈ U ↔ f (invariantBaseMap (G := G) p.2) ∈ U} :=
      (hU.preimage (hf.comp measurable_fst)).iff
        (hU.preimage (hf.comp ((invariantBaseMap_measurable (G := G)).comp measurable_snd)))
    change ∀ᵐ p ∂(μ.map (invariantBaseMap (G := G))) ⊗ₘ invariantBaseKernel (G := G) μ,
      f p.1 ∈ U ↔ f (invariantBaseMap (G := G) p.2) ∈ U
    rw [invariantBaseKernel_joint]
    rw [ae_iff]
    change (μ.map (fun z => (invariantBaseMap (G := G) z,z)))
      ({p : InvariantBase G Z × Z | f p.1 ∈ U ↔ f (invariantBaseMap (G := G) p.2) ∈ U}ᶜ) = 0
    have hgraph : Measurable (fun z : Z => (invariantBaseMap (G := G) z,z)) :=
      (invariantBaseMap_measurable (G := G)).prodMk measurable_id
    rw [Measure.map_apply (μ := μ) hgraph hp.compl]
    change μ {z | ¬ (f (invariantBaseMap (G := G) z) ∈ U ↔
      f (invariantBaseMap (G := G) z) ∈ U)} = 0
    simp
  have h := Measure.ae_ae_of_ae_compProd hj.symm
  exact ae_of_ae_map (invariantBaseMap_measurable (G := G)).aemeasurable h

-- Prove2me | solution 1 for MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_nonsingular
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:27:57.341198+00:00
-- url     : https://prove2.me/submissions/a2b95544-67d6-49b8-96f4-afca038ce910

import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Condexp
import Theorems.Thm_MeasureEquivalenceErgodicDecomposition_invariant_graph_action_eq

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



theorem invariantBaseKernel_joint_map (g : G) (hg : Measurable (fun z : Z => g • z)) :
    (μ.map (invariantBaseMap (G := G))) ⊗ₘ
        (invariantBaseKernel (G := G) μ).map (fun z => g • z) =
      (μ.map (fun z => g • z)).map (fun z => (invariantBaseMap (G := G) z, z)) := by
  rw [Measure.compProd_map hg, invariantBaseKernel_joint]
  have hp : Measurable (Prod.map (id : InvariantBase G Z → InvariantBase G Z)
      (fun z : Z => g • z)) := measurable_id.prodMap hg
  have hgraph : Measurable (fun z : Z => (invariantBaseMap (G := G) z, z)) :=
    (invariantBaseMap_measurable (G := G)).prodMk measurable_id
  rw [Measure.map_map hp hgraph, Measure.map_map hgraph hg]
  simpa only [Function.comp_def, Prod.map_apply, id_eq] using invariant_graph_action_eq μ g hg







end Conditional

end MeasureEquivalenceErgodicDecomposition

end

/-!
The exact invariant sigma-algebra and its actual conditional-probability
kernel. This module establishes invariance and reconstruction; it does
not assert ergodicity of the component probabilities.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
variable [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]

theorem solution
    [MeasurableSpace.CountablyGenerated Z]
    (g : G) (hg : Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ) :
    ∀ᵐ z ∂μ,
      (invariantConditionalKernel (G := G) μ z).map (fun w => g • w) ≪
        invariantConditionalKernel (G := G) μ z := by
  have hmap :
      (μ.map (invariantBaseMap (G := G))) ⊗ₘ
          (invariantBaseKernel (G := G) μ).map (fun z => g • z) ≪
        (μ.map (invariantBaseMap (G := G))) ⊗ₘ invariantBaseKernel (G := G) μ := by
    rw [invariantBaseKernel_joint_map μ g hg.measurable, invariantBaseKernel_joint]
    exact hg.absolutelyContinuous.map
      ((invariantBaseMap_measurable (G := G)).prodMk measurable_id)
  have hAE := Measure.absolutelyContinuous_compProd_right_iff.mp hmap
  have h := ae_of_ae_map (invariantBaseMap_measurable (G := G)).aemeasurable hAE
  simpa only [Kernel.map_apply _ hg.measurable, invariantBaseKernel, invariantConditionalKernel,
    Kernel.comap_apply, invariantBaseMap, id_eq] using h

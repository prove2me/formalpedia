-- Prove2me | solution 1 for MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_stationary
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:25:21.200706+00:00
-- url     : https://prove2.me/submissions/c37c322a-ba89-4301-9c57-86ad978f1bef

import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Tactic
import Theorems.Thm_MeasureEquivalenceErgodicDecomposition_setLIntegral_of_stationary_noLeak

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

/-! A stationary Markov kernel that does not cross invariant sets is
stationary on almost every actual invariant conditional probability. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]
    (P : Kernel Z Z) [IsMarkovKernel P]

theorem solution
    (hstat : P ∘ₘ μ = μ)
    (hleak : ∀ B : Set Z, MeasurableSet B →
      (∀ g : G, (fun z => g • z) ⁻¹' B = B) →
      ∀ᵐ z ∂μ, ∀ᵐ w ∂P z, w ∈ B ↔ z ∈ B) :
    ∀ᵐ x ∂μ, P ∘ₘ invariantConditionalKernel (G := G) μ x =
      invariantConditionalKernel (G := G) μ x := by
  let β := μ.map (invariantBaseMap (G := G))
  let κ := invariantBaseKernel (G := G) μ
  have hj : β ⊗ₘ (P ∘ₖ κ) = β ⊗ₘ κ := by
    apply Measure.ext_prod
    intro B A hB hA
    have hgraph : Measurable (fun z : Z => (invariantBaseMap (G := G) z,z)) :=
      (invariantBaseMap_measurable (G := G)).prodMk measurable_id
    have hi : (∫⁻ z in B, ∫⁻ w, P w A ∂κ z ∂β) =
        ∫⁻ p in B ×ˢ univ, P p.2 A ∂(β ⊗ₘ κ) := by
      symm
      simpa only [Measure.restrict_univ] using
        (Measure.setLIntegral_compProd (μ := β) (κ := κ)
          ((P.measurable_coe hA).comp measurable_snd) hB MeasurableSet.univ)
    have hright : (β ⊗ₘ κ) (B ×ˢ A) = μ ((B:Set Z) ∩ A) := by
      change ((μ.map (invariantBaseMap (G := G))) ⊗ₘ invariantBaseKernel (G := G) μ) _ = _
      rw [invariantBaseKernel_joint, Measure.map_apply hgraph (hB.prod hA)]
      rfl
    rw [Measure.compProd_apply_prod hB hA]
    simp_rw [Kernel.comp_apply' P κ _ hA]
    rw [hi]
    change (∫⁻ p in B ×ˢ univ, P p.2 A ∂(μ.map (invariantBaseMap (G := G))) ⊗ₘ
      invariantBaseKernel (G := G) μ) = _
    have hF : Measurable (fun p : InvariantBase G Z × Z => P p.2 A) :=
      (P.measurable_coe hA).comp measurable_snd
    conv_lhs =>
      rw [invariantBaseKernel_joint,
        Measure.restrict_map hgraph (hB.prod MeasurableSet.univ),
        lintegral_map hF hgraph]
    have hpre : (fun z : Z => (invariantBaseMap (G := G) z,z)) ⁻¹' (B ×ˢ univ) =
        (B:Set Z) := by
      ext z
      change (z ∈ B ∧ z ∈ (univ:Set Z)) ↔ z ∈ B
      simp
    rw [hpre]
    change (∫⁻ z in (B:Set Z), P z A ∂μ) = (β ⊗ₘ κ) (B ×ˢ A)
    exact (setLIntegral_of_stationary_noLeak μ P hstat B A hB.1 hA
      (hleak B hB.1 hB.2)).trans hright.symm
  have hκ : (P ∘ₖ κ) =ᵐ[β] κ := Kernel.ae_eq_of_compProd_eq hj
  have h := ae_of_ae_map (invariantBaseMap_measurable (G := G)).aemeasurable hκ
  exact h

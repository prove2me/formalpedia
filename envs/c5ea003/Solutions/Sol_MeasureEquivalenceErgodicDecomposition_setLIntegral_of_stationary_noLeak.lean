-- Prove2me | solution 1 for MeasureEquivalenceErgodicDecomposition.setLIntegral_of_stationary_noLeak
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:24:24.900254+00:00
-- url     : https://prove2.me/submissions/c14d6e5b-05a4-4986-828c-62b472ee783c

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

/-! A stationary Markov kernel that does not cross invariant sets is
stationary on almost every actual invariant conditional probability. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
variable {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (P : Kernel Z Z) [IsMarkovKernel P]

theorem solution
    (hstat : P ∘ₘ μ = μ) (B A : Set Z) (hB : MeasurableSet B) (hA : MeasurableSet A)
    (hleak : ∀ᵐ z ∂μ, ∀ᵐ w ∂P z, w ∈ B ↔ z ∈ B) :
    (∫⁻ z in B, P z A ∂μ) = μ (B ∩ A) := by
  have hp : MeasurableSet {p : Z × Z | p.2 ∈ B ↔ p.1 ∈ B} :=
    (hB.preimage measurable_snd).iff (hB.preimage measurable_fst)
  have hj := Measure.ae_compProd_of_ae_ae hp hleak
  have hsets : B ×ˢ A =ᵐ[μ ⊗ₘ P] univ ×ˢ (B ∩ A) := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hj] with p hpb
    simp only [mem_prod, mem_univ, true_and, mem_inter_iff]
    tauto
  calc
    _ = (μ ⊗ₘ P) (B ×ˢ A) := (Measure.compProd_apply_prod hB hA).symm
    _ = (μ ⊗ₘ P) (univ ×ˢ (B ∩ A)) := measure_congr hsets
    _ = ∫⁻ z, P z (B ∩ A) ∂μ := by
      simpa only [Measure.restrict_univ] using
        (Measure.compProd_apply_prod (μ := μ) (κ := P) MeasurableSet.univ (hB.inter hA))
    _ = (P ∘ₘ μ) (B ∩ A) := (Measure.bind_apply (hB.inter hA) P.aemeasurable).symm
    _ = _ := congrArg (fun ν : Measure Z => ν (B ∩ A)) hstat

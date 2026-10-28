-- Prove2me | solution 1 for MeasureEquivalenceErgodicDecomposition.measurable_invariant_representative
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:20:44.362693+00:00
-- url     : https://prove2.me/submissions/ea7996c5-79a8-431e-bb6f-e5e458b650a5

import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Condexp

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

/-! Almost-everywhere invariant measurable functions have exactly invariant
measurable representatives for countable group actions. -/
open MeasureTheory ProbabilityTheory Set Filter
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
variable {G Z : Type*} [Group G] [Countable G] [MeasurableSpace Z] [MulAction G Z]
    (μ : Measure Z)

theorem solution (f : Z → ℝ) (hf : Measurable f)
    (haction : ∀ g : G, Measurable (fun z : Z => g • z))
    (hinv : ∀ g : G, (fun z => f (g • z)) =ᵐ[μ] f) :
    ∃ f' : Z → ℝ, Measurable[invariantSigma (G := G)] f' ∧ f' =ᵐ[μ] f := by
  classical
  let S : Set Z := {z | ∀ g : G, f (g • z) = f z}
  have hS : MeasurableSet S := by
    simpa only [S, Function.comp_def, Set.setOf_forall] using
      MeasurableSet.iInter (fun g => measurableSet_eq_fun (hf.comp (haction g)) hf)
  have hgood : ∀ᵐ z ∂μ, z ∈ S := by
    exact ae_all_iff.mpr hinv
  have hSinv (g : G) (z : Z) : g • z ∈ S ↔ z ∈ S := by
    constructor
    · intro hz h
      have hback := hz g⁻¹
      have hh := hz (h*g⁻¹)
      simpa only [mul_smul, inv_smul_smul] using hh.trans hback.symm
    · intro hz h
      have hh : f (h • (g • z)) = f z := by simpa only [mul_smul] using hz (h*g)
      exact hh.trans (hz g).symm
  let f' : Z → ℝ := S.indicator f
  have hf' : Measurable f' := hf.indicator hS
  have hfinv (g : G) (z : Z) : f' (g • z) = f' z := by
    by_cases hz : z ∈ S
    · have hgz := (hSinv g z).mpr hz
      simp only [f', Set.indicator_of_mem hz, Set.indicator_of_mem hgz]
      exact hz g
    · have hgz : g • z ∉ S := fun h => hz ((hSinv g z).mp h)
      simp only [f', Set.indicator_of_notMem hz, Set.indicator_of_notMem hgz]
  refine ⟨f', ?_, ?_⟩
  · intro U hU
    refine ⟨hU.preimage hf', ?_⟩
    intro g
    ext z
    change f' (g • z) ∈ U ↔ f' z ∈ U
    rw [hfinv]
  · exact hgood.mono (fun _ hz => Set.indicator_of_mem hz f)

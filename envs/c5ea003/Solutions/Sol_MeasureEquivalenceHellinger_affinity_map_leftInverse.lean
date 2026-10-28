-- Prove2me | solution 1 for MeasureEquivalenceHellinger.affinity_map_leftInverse
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:25:11.305102+00:00
-- url     : https://prove2.me/submissions/b5618ed4-9077-4ef6-9192-a58aa07993c7

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
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

-- Preserved source skeleton: SharedConditionalDensity
section
/-! The actual invariant conditional probabilities share the ambient
Radon--Nikodym derivatives. No unbounded-density kernel is postulated. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceSharedDensity

section Push

variable {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]

theorem map_withDensity_comp (M : Measure Z) (j : Z → W) (hj : Measurable j)
    (F : W → ℝ≥0∞) (hF : Measurable F) :
    (M.withDensity (fun z => F (j z))).map j = (M.map j).withDensity F := by
  ext s hs
  rw [Measure.map_apply hj hs, withDensity_apply _ (hs.preimage hj), withDensity_apply _ hs,
    ← lintegral_indicator (hs.preimage hj), ← lintegral_indicator hs,
    lintegral_map (hF.indicator hs) hj]
  rfl

end Push

section Joint

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    (β : Measure Y) [IsFiniteMeasure β] (M : Measure Z) [IsFiniteMeasure M]
    (κ : Kernel Y Z) [IsFiniteKernel κ] (q : Z → Y) (hq : Measurable q)
    (hJ : β ⊗ₘ κ = M.map (fun z => (q z,z)))



end Joint

section Invariant

open MeasureEquivalenceErgodicDecomposition

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]



end Invariant

end MeasureEquivalenceSharedDensity

end

-- Preserved source skeleton: HellingerSplitMap
section
/-! Affinity is preserved by a measurable map with a measurable left inverse.
The target need not be standard Borel, which allows the invariant sigma algebra. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]

theorem rnDeriv_map_leftInverse (j : Z → W) (hj : Measurable j)
    (r : W → Z) (hr : Measurable r) (hleft : Function.LeftInverse r j)
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac : μ ≪ ν) :
    (fun z => (μ.map j).rnDeriv (ν.map j) (j z)) =ᵐ[ν] μ.rnDeriv ν := by
  let F : W → ℝ≥0∞ := fun w => μ.rnDeriv ν (r w)
  have hF : Measurable F := (Measure.measurable_rnDeriv _ _).comp hr
  have hD : ν.withDensity (fun z => F (j z)) = μ := by
    have heF : (fun z => F (j z)) = μ.rnDeriv ν :=
      funext (fun z => congrArg (μ.rnDeriv ν) (hleft z))
    rw [heF]
    exact Measure.withDensity_rnDeriv_eq μ ν hac
  have hDj : (ν.map j).withDensity F = μ.map j := by
    rw [← MeasureEquivalenceSharedDensity.map_withDensity_comp ν j hj F hF, hD]
  have hRN := (ν.map j).rnDeriv_withDensity hF
  rw [hDj] at hRN
  have hp := ae_of_ae_map hj.aemeasurable hRN
  filter_upwards [hp] with z hz
  exact hz.trans (congrArg (μ.rnDeriv ν) (hleft z))



end MeasureEquivalenceHellinger

end

/-! Affinity is preserved by a measurable map with a measurable left inverse.
The target need not be standard Borel, which allows the invariant sigma algebra. -/
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
open MeasureEquivalenceHellinger
variable {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]

theorem solution (j : Z → W) (hj : Measurable j)
    (r : W → Z) (hr : Measurable r) (hleft : Function.LeftInverse r j)
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    affinity (μ.map j) (ν.map j) = affinity μ ν := by
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  rw [affinity_eq_affinityAgainst (μ.map j) (ν.map j) ((μ+ν).map j)
    (hμ.map hj) (hν.map hj)]
  unfold affinityAgainst
  rw [integral_map hj.aemeasurable
    (((Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt.mul
      (Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt).aestronglyMeasurable)]
  rw [affinity_integral]
  apply integral_congr_ae
  filter_upwards [rnDeriv_map_leftInverse j hj r hr hleft μ (μ+ν) hμ,
    rnDeriv_map_leftInverse j hj r hr hleft ν (μ+ν) hν] with z hm hn
  rw [hm, hn]

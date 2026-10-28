-- Prove2me | solution 1 for MeasureUnitary.exists_faithful_L2
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:25:01.425875+00:00
-- url     : https://prove2.me/submissions/a0b60206-3472-4992-a273-69785c812127

import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryRN
import Definitions.Def_BenchmarkOperator20261026_VectorSpectralState
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

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

/-! Finite vector-state measures and faithful vectors in actual sigma-finite
L² spaces. These give measure-class reflection without postulating a spectral theorem. -/
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal
namespace MeasureUnitary
end MeasureUnitary
open MeasureUnitary
variable {Ω Λ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace X]

theorem solution (μ : Measure Ω) [SigmaFinite μ] :
    ∃ f : Lp ℂ 2 μ, ∀ᵐ x ∂μ, f x ≠ 0 := by
  obtain ⟨ν,hν,hμν,hνμ⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  letI : IsFiniteMeasure ν := hν
  let f := rnWeightedMap ν μ hνμ hμν (constantOneL2 ν)
  refine ⟨f,?_⟩
  filter_upwards [rnWeightedMap_coe ν μ hνμ hμν (constantOneL2 ν),
    hμν.ae_eq (constantOneL2_coe ν), rnWeight_inverse_product μ ν hμν hνμ]
    with x hfx h1 hp
  change f x ≠ 0
  rw [hfx,h1]
  apply smul_ne_zero
  · intro hz
    simp [hz] at hp
  · exact one_ne_zero

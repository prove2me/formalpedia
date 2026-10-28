-- Prove2me | solution 1 for MeasureEquivalenceErgodicDecomposition.determiningSet_generates
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:20:22.995188+00:00
-- url     : https://prove2.me/submissions/f018ad39-45ff-4a74-8e2b-42f71a7186a8

import Definitions.Def_BenchmarkOperator20261026_ConditionalFibers
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

-- Preserved source skeleton: ConditionalFibers
section
/-! The actual invariant conditional kernel is constant almost everywhere
on almost every conditional fiber. Countability is used only for a family
that determines finite measures, so no AE/uncountable-forall swap is made. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceErgodicDecomposition

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]





theorem determiningSet_measurable (s : Finset ℕ) : MeasurableSet (determiningSet (Z := Z) s) :=
  s.measurableSet_biInter (fun i _hi => MeasurableSpace.measurableSet_natGeneratingSequence (α := Z) i)











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

theorem solution :
    MeasurableSpace.generateFrom (range (determiningSet (Z := Z))) = ‹MeasurableSpace Z› := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro B hB
    rcases hB with ⟨s, rfl⟩
    exact determiningSet_measurable s
  · have hs : range (MeasurableSpace.natGeneratingSequence Z) ⊆
        range (determiningSet (Z := Z)) := by
      rintro _ ⟨n, rfl⟩
      exact ⟨{n}, by ext z; simp [determiningSet]⟩
    exact (MeasurableSpace.generateFrom_natGeneratingSequence (α := Z)).symm.le.trans
      (MeasurableSpace.generateFrom_mono hs)

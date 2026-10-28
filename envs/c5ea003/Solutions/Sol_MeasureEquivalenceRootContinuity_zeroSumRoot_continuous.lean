-- Prove2me | solution 1 for MeasureEquivalenceRootContinuity.zeroSumRoot_continuous
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:13:39.479429+00:00
-- url     : https://prove2.me/submissions/f6b24e78-2047-4691-8a6b-21f087e6fb27

import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_RootContinuity
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish
import Theorems.Thm_MeasureEquivalenceRootContinuity_continuous_root_of_mem

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

-- Preserved source skeleton: SolenoidGroups
section
/-! The compact solenoid group and its real-sequence embedding from Section 8.
This file contains supporting lemmas, not the operator separation theorem. -/

open Filter Topology TopologicalSpace
open scoped Topology ENNReal

namespace MeasureEquivalenceSolenoid

noncomputable section












































theorem l1Embedding_continuous : Continuous l1Embedding := by
  apply sequenceEmbedding_continuous.comp
  apply continuous_pi
  intro n
  exact (lp.lipschitzWith_one_eval (E := fun _ : ℕ => ℝ) (1:ℝ≥0∞) n).continuous


















































end
end MeasureEquivalenceSolenoid

end

-- Preserved source skeleton: RootContinuity
section
/-! Actual Radon--Nikodym root continuity for the zero-sum l1 subgroup.
The general closed-graph argument is reused from the archived sequence-space
development. No continuity of densities is assumed. -/

open MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceRootContinuity

open MeasureEquivalenceDensity MeasureEquivalenceHellinger
open MeasureEquivalenceRNGraph MeasureEquivalenceInvariantGraph

section General

variable {A Z G : Type*}
    [CommGroup A] [MetricSpace A] [IsTopologicalGroup A]
    [CompleteSpace A] [SecondCountableTopology A]
    [MeasurableSpace Z] [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction A Z] [ContinuousSMul A Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]



end General

open MeasureEquivalenceSolenoid



theorem zeroSumInclusion_continuous : Continuous zeroSumInclusion :=
  l1Embedding_continuous.comp continuous_subtype_val

section ActualAction

variable {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]
    (M : Measure Z) [IsProbabilityMeasure M]





end ActualAction

end MeasureEquivalenceRootContinuity

end

/-! Actual Radon--Nikodym root continuity for the zero-sum l1 subgroup.
The general closed-graph argument is reused from the archived sequence-space
development. No continuity of densities is assumed. -/
open MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal
namespace MeasureEquivalenceRootContinuity
end MeasureEquivalenceRootContinuity
open MeasureEquivalenceRootContinuity
open MeasureEquivalenceDensity MeasureEquivalenceHellinger
open MeasureEquivalenceRNGraph MeasureEquivalenceInvariantGraph
open MeasureEquivalenceSolenoid
variable {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]
    (M : Measure Z) [IsProbabilityMeasure M]

theorem solution
    (hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M) :
    Continuous (zeroSumRoot M) := by
  letI : PolishSpace (Multiplicative CompactSequences) :=
    inferInstanceAs (PolishSpace CompactSequences)
  letI := upgradeIsCompletelyMetrizable (Multiplicative CompactSequences)
  letI : PolishSpace (Multiplicative zeroSumSpace) :=
    inferInstanceAs (PolishSpace zeroSumSpace)
  letI : MeasurableSpace (Multiplicative zeroSumSpace) := borel (Multiplicative zeroSumSpace)
  letI : BorelSpace (Multiplicative zeroSumSpace) := ⟨rfl⟩
  let i : Multiplicative zeroSumSpace →* Multiplicative CompactSequences :=
    AddMonoidHom.toMultiplicative zeroSumInclusion
  have hi : Continuous i := zeroSumInclusion_continuous
  have hm (h : Multiplicative zeroSumSpace) : i h ∈ quasiInvariantSubgroup M :=
    hQI _ ⟨h.toAdd, h.toAdd.property, rfl⟩
  exact continuous_root_of_mem M i hi hm

-- Prove2me | Definitions.Def_BenchmarkOperator20261026_ZeroSumConditional
-- name    : BenchmarkOperator20261026_ZeroSumConditional
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:53:12.112408+00:00
-- url     : https://prove2.me/theorems/97494569-ff0b-4145-a4c3-0a688746fb1a
-- title:
--   Zero Sum Conditional
-- statement:
--   Defines the countable rational zero-sum group, its embedding into the compact sequence group, the induced action and the invariant conditional kernel for that action. The structure instances needed to form this component kernel are retained. Component affinity identities are separate theorems.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization ZeroSumConditional.lean, lines 18–48; source SHA-256 6aee509cbc53b50fe3e0040bd3c9b4ed7dcc500a12ddb093f3d10b4005854a06. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HellingerInner
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_RootContinuity
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_ZeroSumDense
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Data.Finsupp.Encodable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Semicontinuity.Basic

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

/-! The actual dense rational zero-sum conditional kernel and its
unconditional affinity disintegration for all intrinsic zero-sum shifts. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped ENNReal

namespace MeasureEquivalenceRigidity

noncomputable section

open MeasureEquivalenceSolenoid MeasureEquivalenceRootContinuity
  MeasureEquivalenceRNGraph MeasureEquivalenceHellinger
  MeasureEquivalenceErgodicDecomposition MeasureEquivalenceDenseInvariance

def zeroSumGroupHom : Multiplicative zeroSumSpace →* Multiplicative CompactSequences :=
  AddMonoidHom.toMultiplicative zeroSumInclusion

def rationalZeroSumGroup : Subgroup (Multiplicative zeroSumSpace) where
  carrier := {g | g.toAdd ∈ denseRationalSubgroup}
  one_mem' := denseRationalSubgroup.zero_mem
  mul_mem' := denseRationalSubgroup.add_mem
  inv_mem' := denseRationalSubgroup.neg_mem



instance rationalZeroSumGroup_countable : Countable rationalZeroSumGroup :=
  denseRationalSubgroup_countable.to_subtype

variable {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]

abbrev rationalZeroSumAction : MulAction rationalZeroSumGroup Z :=
  MulAction.compHom Z (zeroSumGroupHom.comp rationalZeroSumGroup.subtype)

noncomputable def zeroSumComponentKernel (M : Measure Z) [IsProbabilityMeasure M] : Kernel Z Z :=
  letI : MulAction rationalZeroSumGroup Z := rationalZeroSumAction
  invariantConditionalKernel (G := rationalZeroSumGroup) M

instance zeroSumComponentKernel_markov (M : Measure Z) [IsProbabilityMeasure M] :
    IsMarkovKernel (zeroSumComponentKernel M) := by
  unfold zeroSumComponentKernel
  infer_instance

variable (M : Measure Z) [IsProbabilityMeasure M]
    (hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M)





end
end MeasureEquivalenceRigidity



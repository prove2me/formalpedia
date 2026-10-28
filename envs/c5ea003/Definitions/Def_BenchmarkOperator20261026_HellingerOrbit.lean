-- Prove2me | Definitions.Def_BenchmarkOperator20261026_HellingerOrbit
-- name    : BenchmarkOperator20261026_HellingerOrbit
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:29:33.27879+00:00
-- url     : https://prove2.me/theorems/93188f17-c720-4d14-baf3-58ae6a416cab
-- title:
--   Hellinger Orbit
-- statement:
--   Defines the action on the second coordinate of a product and the probability-measure orbit associated with it. The later upper-semicontinuity theorem applies Hellinger affinity to these orbit measures.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization HellingerOrbit.lean, lines 23–40; source SHA-256 51c41b99f1303be86216725e2e2b3020877e4322d582a58008fc9425b0664e53. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
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

/-! Upper semicontinuity of averaged component affinities, obtained by
applying the actual affinity theorem to an equal-marginal joint measure. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceHellinger

section Orbit

variable {K Z : Type*} [Group K] [TopologicalSpace K] [FirstCountableTopology K]
    [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    (M : Measure Z) [IsProbabilityMeasure M]

def probabilityOrbit (g : K) : ProbabilityMeasure Z :=
  ⟨M.map (fun z => g • z), M.isProbabilityMeasure_map (measurable_const_smul g).aemeasurable⟩



end Orbit

abbrev rightCoordinateAction (K Y Z : Type*) [Monoid K] [MulAction K Z] :
    MulAction K (Y × Z) where
  smul g p := (p.1, g • p.2)
  one_smul p := by
    change (p.1, (1:K) • p.2) = p
    simp
  mul_smul g h p := by
    change (p.1, (g*h) • p.2) = (p.1, g • (h • p.2))
    rw [mul_smul]



section Averaged

variable {K Y Z : Type*} [Group K] [TopologicalSpace K] [FirstCountableTopology K]
    [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    (η : Measure Y) [IsProbabilityMeasure η] (κ : Kernel Y Z) [IsMarkovKernel κ]



end Averaged

section StandardBorelAverage

variable {K Y Z : Type*} [Group K] [TopologicalSpace K] [FirstCountableTopology K]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    (η : Measure Y) [IsProbabilityMeasure η] (κ : Kernel Y Z) [IsMarkovKernel κ]



end StandardBorelAverage

end MeasureEquivalenceHellinger



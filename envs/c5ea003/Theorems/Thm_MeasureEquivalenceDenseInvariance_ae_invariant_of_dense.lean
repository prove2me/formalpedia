-- Prove2me | Theorems.Thm_MeasureEquivalenceDenseInvariance_ae_invariant_of_dense
-- name    : MeasureEquivalenceDenseInvariance.ae_invariant_of_dense
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:56:47.196689+00:00
-- url     : https://prove2.me/theorems/8914d7cd-ed9f-4cb7-a5c5-55ff31e8583b
-- title:
--   Almost-everywhere invariance extends from a dense subgroup parameter set
-- statement:
--   Let a commutative separable complete metric topological group $A$ act continuously on a Polish space $Z$, and let $M$ be a Borel probability measure. Let $G$ be a Polish group and $i:G\to A$ a continuous homomorphism whose image preserves the measure class of $M$. If a measurable set $S\subseteq Z$ satisfies
--   $$i(d)^{-1}S=S\pmod M\qquad(d\in D)$$
--   for a dense set $D\subseteq G$, then the same identity holds for every $g\in G$. This extends measurable invariance to the intrinsic group closure.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceDenseInvariance.ae_invariant_of_dense in DenseInvariantSets.lean, lines 28–54; local source SHA-256 13b9b7f9a1ef03e2a2238ba57e7d0fb7e0225bafe375cd9edf7093a7ac63b100. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_ZeroSumDense
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Data.Finsupp.Encodable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
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
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish

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

/-! Measurable invariant sets persist under the intrinsic Polish group closure.
The proof uses actual restricted measures and the continuity of RN roots;
it does not assume continuity of a Koopman representation. -/
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal
namespace MeasureEquivalenceDenseInvariance
end MeasureEquivalenceDenseInvariance
open MeasureEquivalenceDenseInvariance
open MeasureEquivalenceDensity MeasureEquivalenceHellinger
open MeasureEquivalenceRNGraph MeasureEquivalenceRootContinuity
open MeasureEquivalenceRestrictedRoots
variable {A Z G : Type*}
    [CommGroup A] [MetricSpace A] [IsTopologicalGroup A]
    [CompleteSpace A] [SecondCountableTopology A]
    [MeasurableSpace Z] [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction A Z] [ContinuousSMul A Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]

theorem MeasureEquivalenceDenseInvariance.ae_invariant_of_dense (i : G →* A) (hi : Continuous i)
    (hmem : ∀ g, i g ∈ quasiInvariantSubgroup (K := A) M)
    (D : Set G) (hD : Dense D) (s : Set Z) (hs : MeasurableSet s)
    (hinv : ∀ d ∈ D, (fun z => i d • z) ⁻¹' s =ᵐ[M] s) :
    ∀ g : G, (fun z => i g • z) ⁻¹' s =ᵐ[M] s := by sorry

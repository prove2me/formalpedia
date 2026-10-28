-- Prove2me | Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
-- name    : BenchmarkOperator20261026_InvariantGraphGroup
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:28:56.812693+00:00
-- url     : https://prove2.me/theorems/9dea7587-88a5-41d5-87f1-0093872bc50d
-- title:
--   Invariant Graph Group
-- statement:
--   Defines a graph-metric presentation of a subgroup with a metric-space feature map, together with its group structure, inclusion and graph maps. The injectivity facts needed to pull back the product metric are retained. The topological-group theorem is published separately.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization InvariantGraphGroup.lean, lines 11–32; source SHA-256 02f095837c638c1dace11e4ece015f7ee6e3ec7502fb136c8decb253fdda3444. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable

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

open Set
open scoped Topology

namespace MeasureEquivalenceInvariantGraph

variable {K V : Type*} [CommGroup K] [MetricSpace K]
    [MetricSpace V] (H : Subgroup K) (r : H → V)

/-- A separate presentation of H, carrying the graph metric rather than its
possibly incomplete subspace metric from K. -/
def GraphGroup (_r : H → V) : Type _ := H

instance _root_.MeasureEquivalenceInvariantGraph.instCommGroupGraphGroup : CommGroup (GraphGroup H r) := inferInstanceAs (CommGroup H)

def inclusion (h : GraphGroup H r) : K := (show H from h)

def graph (h : GraphGroup H r) : K × V := (inclusion H r h, r h)

omit [MetricSpace K] [MetricSpace V] in
theorem inclusion_injective : Function.Injective (inclusion H r) := by
  intro a b hab
  exact Subtype.ext hab

omit [MetricSpace K] [MetricSpace V] in
theorem graph_injective : Function.Injective (graph H r) := by
  intro a b hab
  exact inclusion_injective H r (congrArg Prod.fst hab)

noncomputable instance _root_.MeasureEquivalenceInvariantGraph.instMetricSpaceGraphGroup : MetricSpace (GraphGroup H r) :=
  MetricSpace.induced (graph H r) (graph_injective H r) inferInstance









variable (hleft : ∀ a h k : H, dist (r (a * h)) (r (a * k)) = dist (r h) (r k))













section Presentation

variable [IsTopologicalGroup K] [CompleteSpace K] [CompleteSpace V]
    [SecondCountableTopology K] [SecondCountableTopology V]
    (hclosed : IsClosed (Set.range (fun h : H => ((h : K), r h))))
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]





end Presentation

end MeasureEquivalenceInvariantGraph



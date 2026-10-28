-- Prove2me | Theorems.Thm_MeasureEquivalenceInvariantGraph_graphGroup_topologicalGroup
-- name    : MeasureEquivalenceInvariantGraph.graphGroup_topologicalGroup
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:54:56.376605+00:00
-- url     : https://prove2.me/theorems/ddf0a068-f917-4636-b08f-d71a085b960e
-- title:
--   The graph metric makes the subgroup a topological group
-- statement:
--   Let $K$ be a commutative metric topological group, $H\leq K$, and $r:H\to V$ a map to a metric space. Assume that left multiplication preserves feature distances:
--   $$d_V(r(ah),r(ak))=d_V(r(h),r(k))\qquad(a,h,k\in H).$$
--   Equip $H$ with the metric induced by $h\mapsto(h,r(h))$ into $K\times V$. With its inherited group operations, this graph-metric presentation of $H$ is a topological group. This supplies a compatible group topology for the density graph.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceInvariantGraph.graphGroup_topologicalGroup in InvariantGraphGroup.lean, lines 65–88; local source SHA-256 02f095837c638c1dace11e4ece015f7ee6e3ec7502fb136c8decb253fdda3444. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
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
end MeasureEquivalenceInvariantGraph
open MeasureEquivalenceInvariantGraph
variable {K V : Type*} [CommGroup K] [MetricSpace K]
    [MetricSpace V] (H : Subgroup K) (r : H → V)
variable (hleft : ∀ a h k : H, dist (r (a * h)) (r (a * k)) = dist (r h) (r k))

include hleft

theorem MeasureEquivalenceInvariantGraph.graphGroup_topologicalGroup [IsTopologicalGroup K] : IsTopologicalGroup (GraphGroup H r) := by sorry

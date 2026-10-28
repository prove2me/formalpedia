-- Prove2me | Theorems.Thm_MeasureEquivalenceDensityGraph_isClosed_density_graph
-- name    : MeasureEquivalenceDensityGraph.isClosed_density_graph
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:55:06.936487+00:00
-- url     : https://prove2.me/theorems/b5ee1904-1292-4619-a43b-2bf8a37cb2d0
-- title:
--   Closedness of an abstract density graph
-- statement:
--   Let $K$ be a metric topological group, $V$ a complete metric space, $P$ a Hausdorff space, and $H\leq K$. Suppose continuous maps $\mu:K\to P$ and $\nu:V\to P$, with $\nu$ injective, satisfy
--   $$\nu(r(h))=\mu(h)\qquad(h\in H).$$
--   Let $A$ be a predicate on $P$ that holds on every $\nu(v)$, and assume
--   $$g\in H\ \Longleftrightarrow\ A(\mu(g))\ \text{and}\ A(\mu(g^{-1})).$$
--   If inversion on $H$ preserves the distances of its $r$-images, then the graph $\{(h,r(h)):h\in H\}$ is closed in $K\times V$. The lemma isolates the closed-graph argument used for square-root densities.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceDensityGraph.isClosed_density_graph in DensityGraphCompleteness.lean, lines 23–61; local source SHA-256 b2bcfbd0193cce734cf1ca0769170bf2a7d8febfbf7a55af8a9d9dc8b60c96d5. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
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

/-!
# Abstract density-graph completeness

This verifies the inverse-sequence / closed-graph argument with explicit
analytical interface hypotheses. It does not construct square-root RN densities
or verify those analytical interface hypotheses for L2 measures.
-/
open Filter Set
open scoped Topology
namespace MeasureEquivalenceDensityGraph
end MeasureEquivalenceDensityGraph
open MeasureEquivalenceDensityGraph
variable {K V P : Type*} [Group K] [MetricSpace K] [IsTopologicalGroup K]
  [MetricSpace V] [CompleteSpace V] [TopologicalSpace P] [T2Space P]

theorem MeasureEquivalenceDensityGraph.isClosed_density_graph (H : Subgroup K) (r : H → V)
    (μ : K → P) (ν : V → P) (A : P → Prop)
    (hμ : Continuous μ) (hν : Continuous ν) (hνinj : Function.Injective ν)
    (hfactor : ∀ h : H, ν (r h) = μ (h : K))
    (hA : ∀ v : V, A (ν v))
    (hH : ∀ g : K, g ∈ H ↔ A (μ g) ∧ A (μ g⁻¹))
    (hinv : ∀ h k : H, dist (r h⁻¹) (r k⁻¹) = dist (r h) (r k)) :
    IsClosed (Set.range (fun h : H => ((h : K), r h))) := by sorry

-- Prove2me | solution 1 for MeasureEquivalenceInvariantGraph.graphGroup_topologicalGroup
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:14:31.020921+00:00
-- url     : https://prove2.me/submissions/1cf70a0a-40cb-4c6a-a53a-482ca639d8ca

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

-- Preserved source skeleton: InvariantGraphGroup
section
open Set
open scoped Topology

namespace MeasureEquivalenceInvariantGraph

variable {K V : Type*} [CommGroup K] [MetricSpace K]
    [MetricSpace V] (H : Subgroup K) (r : H → V)















theorem graph_isometry : Isometry (graph H r) := Isometry.of_dist_eq (fun _ _ => rfl)

theorem inclusion_continuous : Continuous (inclusion H r) :=
  continuous_fst.comp (graph_isometry H r).continuous



theorem feature_dist_le (a b : GraphGroup H r) : dist (r a) (r b) ≤ dist a b := by
  change dist (r a) (r b) ≤ max (dist (inclusion H r a) (inclusion H r b)) (dist (r a) (r b))
  exact le_max_right _ _

variable (hleft : ∀ a h k : H, dist (r (a * h)) (r (a * k)) = dist (r h) (r k))

include hleft in
omit [MetricSpace K] in
theorem feature_inverse (h k : H) : dist (r h⁻¹) (r k⁻¹) = dist (r h) (r k) := by
  have hi := hleft (h * k) h⁻¹ k⁻¹
  have hh : h * k * h⁻¹ = k := by simp
  have hk : h * k * k⁻¹ = h := by group
  rw [hh, hk] at hi
  exact hi.symm.trans (dist_comm _ _)

include hleft in
omit [MetricSpace K] in
theorem feature_mul_bound (a b c d : H) :
    dist (r (a * b)) (r (c * d)) ≤ dist (r a) (r c) + dist (r b) (r d) := by
  calc
    _ ≤ dist (r (a * b)) (r (c * b)) + dist (r (c * b)) (r (c * d)) := dist_triangle _ _ _
    _ = _ := by rw [hleft, mul_comm a b, mul_comm c b, hleft]









section Presentation

variable [IsTopologicalGroup K] [CompleteSpace K] [CompleteSpace V]
    [SecondCountableTopology K] [SecondCountableTopology V]
    (hclosed : IsClosed (Set.range (fun h : H => ((h : K), r h))))
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]





end Presentation

end MeasureEquivalenceInvariantGraph

end

open Set
open scoped Topology
namespace MeasureEquivalenceInvariantGraph
end MeasureEquivalenceInvariantGraph
open MeasureEquivalenceInvariantGraph
variable {K V : Type*} [CommGroup K] [MetricSpace K]
    [MetricSpace V] (H : Subgroup K) (r : H → V)
variable (hleft : ∀ a h k : H, dist (r (a * h)) (r (a * k)) = dist (r h) (r k))

include hleft

theorem solution [IsTopologicalGroup K] : IsTopologicalGroup (GraphGroup H r) where
  continuous_mul := by
    apply (graph_isometry H r).isEmbedding.continuous_iff.mpr
    have hr : LipschitzWith 2 (fun p : GraphGroup H r × GraphGroup H r => r (p.1 * p.2)) := by
      apply LipschitzWith.of_dist_le_mul
      intro p q
      have hb := feature_mul_bound H r hleft p.1 p.2 q.1 q.2
      have h1 := feature_dist_le H r p.1 q.1
      have h2 := feature_dist_le H r p.2 q.2
      have h3 := le_max_left (dist p.1 q.1) (dist p.2 q.2)
      have h4 := le_max_right (dist p.1 q.1) (dist p.2 q.2)
      simp only [NNReal.coe_ofNat, Prod.dist_eq]
      exact hb.trans ((add_le_add h1 h2).trans (by linarith))
    exact (((inclusion_continuous H r).comp continuous_fst).mul
      ((inclusion_continuous H r).comp continuous_snd)).prodMk hr.continuous
  continuous_inv := by
    apply (graph_isometry H r).isEmbedding.continuous_iff.mpr
    have hr : LipschitzWith 1 (fun p : GraphGroup H r => r p⁻¹) := by
      apply LipschitzWith.of_dist_le_mul
      intro p q
      simp only [NNReal.coe_one, one_mul]
      exact (feature_inverse H r hleft p q).le.trans (feature_dist_le H r p q)
    exact (inclusion_continuous H r).inv.prodMk hr.continuous

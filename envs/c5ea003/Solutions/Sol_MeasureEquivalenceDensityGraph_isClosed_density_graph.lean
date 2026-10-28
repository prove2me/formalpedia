-- Prove2me | solution 1 for MeasureEquivalenceDensityGraph.isClosed_density_graph
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:15:38.648779+00:00
-- url     : https://prove2.me/submissions/3b45e277-a7d3-4ed2-af49-559ff72b24aa

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

theorem solution (H : Subgroup K) (r : H → V)
    (μ : K → P) (ν : V → P) (A : P → Prop)
    (hμ : Continuous μ) (hν : Continuous ν) (hνinj : Function.Injective ν)
    (hfactor : ∀ h : H, ν (r h) = μ (h : K))
    (hA : ∀ v : V, A (ν v))
    (hH : ∀ g : K, g ∈ H ↔ A (μ g) ∧ A (μ g⁻¹))
    (hinv : ∀ h k : H, dist (r h⁻¹) (r k⁻¹) = dist (r h) (r k)) :
    IsClosed (Set.range (fun h : H => ((h : K), r h))) := by
  have limit_identity {u : ℕ → H} {g : K} {v : V}
      (hu : Tendsto (fun n => (u n : K)) atTop (𝓝 g))
      (hv : Tendsto (fun n => r (u n)) atTop (𝓝 v)) : μ g = ν v := by
    have hp := hμ.continuousAt.tendsto.comp hu
    have hq := hν.continuousAt.tendsto.comp hv
    exact tendsto_nhds_unique hp (by simpa only [Function.comp_def, hfactor] using hq)
  apply isSeqClosed_iff_isClosed.mp
  intro s p hs hp
  choose u hu using hs
  have hlim : Tendsto (fun n => ((u n : K), r (u n))) atTop (𝓝 p) := by
    simpa only [hu] using hp
  have hK := (continuous_fst.tendsto p).comp hlim
  have hV := (continuous_snd.tendsto p).comp hlim
  have hforward : μ p.1 = ν p.2 := limit_identity hK hV
  have hC : CauchySeq (fun n => r ((u n)⁻¹)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hV.cauchySeq ε hε
    exact ⟨N, fun i hi j hj => by rw [hinv]; exact hN i hi j hj⟩
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hC
  have hKinv : Tendsto (fun n => (((u n)⁻¹ : H) : K)) atTop (𝓝 p.1⁻¹) := by
    simpa only [Subgroup.coe_inv, Function.comp_def] using hK.inv
  have hback : μ p.1⁻¹ = ν w := limit_identity hKinv hw
  have hpH : p.1 ∈ H := (hH p.1).mpr ⟨hforward.symm ▸ hA p.2, hback.symm ▸ hA w⟩
  refine ⟨⟨p.1, hpH⟩, ?_⟩
  apply Prod.ext
  · rfl
  · apply hνinj
    exact (hfactor ⟨p.1, hpH⟩).trans hforward

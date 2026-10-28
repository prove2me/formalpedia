-- Prove2me | solution 1 for MeasureEquivalenceTopology.pettis_nhds_one
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:16:43.890304+00:00
-- url     : https://prove2.me/submissions/d3443d53-2201-43bf-82a6-d6ac431fd6a0

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

/-!
Pettis category, Borel-homomorphism continuity, and uniqueness of compatible
Polish group topologies. This is a new standalone verification development.
-/
open Filter Set TopologicalSpace
open scoped Topology Pointwise
namespace MeasureEquivalenceTopology
end MeasureEquivalenceTopology
open MeasureEquivalenceTopology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BaireSpace G]

theorem solution {A : Set G} (hA : BaireMeasurableSet A)
    (hnot : ¬ IsMeagre A) : A / A ∈ 𝓝 (1 : G) := by
  obtain ⟨U, hU, hAU⟩ := hA.residualEq_isOpen
  have hprop : ∀ᵇ x, x ∈ A ↔ x ∈ U := Filter.eventuallyEq_set.mp hAU
  have hUne : U.Nonempty := by
    by_contra h
    have hzero : U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    apply hnot
    change Aᶜ ∈ residual G
    filter_upwards [hprop] with x hx
    intro hxA
    have hxU := hx.mp hxA
    simp [hzero] at hxU
  obtain ⟨u, hu⟩ := hUne
  let W : Set G := {g | g⁻¹ * u ∈ U}
  have hW : W ∈ 𝓝 (1 : G) := by
    apply (hU.preimage (by fun_prop : Continuous (fun g : G => g⁻¹ * u))).mem_nhds
    simpa using hu
  apply Filter.mem_of_superset hW
  intro g hg
  have htrans : ∀ᵇ x, g⁻¹ * x ∈ A ↔ g⁻¹ * x ∈ U :=
    (tendsto_residual_of_isOpenMap
      (by fun_prop : Continuous (fun x : G => g⁻¹ * x))
      (isOpenMap_mul_left g⁻¹)) hprop
  let B : Set G := U ∩ (fun x : G => g⁻¹ * x) ⁻¹' U
  have hB : IsOpen B := hU.inter (hU.preimage (by fun_prop))
  have hBne : B.Nonempty := ⟨u, hu, hg⟩
  have hd : Dense {x : G | (x ∈ A ↔ x ∈ U) ∧
      (g⁻¹ * x ∈ A ↔ g⁻¹ * x ∈ U)} :=
    dense_of_mem_residual (hprop.and htrans)
  obtain ⟨x, hxB, hxR⟩ := hd.inter_open_nonempty B hB hBne
  refine Set.mem_div.mpr ⟨x, hxR.1.mpr hxB.1, g⁻¹ * x, hxR.2.mpr hxB.2, ?_⟩
  simp [div_eq_mul_inv]

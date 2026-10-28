-- Prove2me | solution 1 for MeasureEquivalenceRestrictedProduct.map_add_eq_of_dense_invariant
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:33:32.684934+00:00
-- url     : https://prove2.me/submissions/b8a34a96-9d21-40e2-a9e6-f284376d3300

import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic
import Mathlib.Topology.CompactOpen

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

open MeasureTheory Set Filter
open scoped Topology
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G]

theorem solution (μ : Measure G) [μ.Regular]
    (D : Set G) (hD : Dense D)
    (hinv : ∀ q ∈ D, μ.map (fun x => x + q) = μ) (h : G) :
    μ.map (fun x => x + h) = μ := by
  let A : C(G × G, G) := ⟨fun p => p.2 + p.1, continuous_snd.add continuous_fst⟩
  have hle (a : G) (U : Set G) (hU : IsOpen U) : μ ((fun x => x + a) ⁻¹' U) ≤ μ U := by
    rw [(hU.preimage (show Continuous (fun x : G => x + a) from by fun_prop)).measure_eq_iSup_isCompact μ]
    apply iSup_le
    intro K
    apply iSup_le
    intro hKU
    apply iSup_le
    intro hK
    have he : ∀ᶠ q in 𝓝 a, MapsTo (A.curry q) K U :=
      (A.curry.continuous.tendsto a).eventually (ContinuousMap.eventually_mapsTo hK hU hKU)
    obtain ⟨q, hqD, hqK⟩ := hD.inter_nhds_nonempty he
    calc
      μ K ≤ μ ((fun x : G => x + q) ⁻¹' U) := measure_mono hqK
      _ = μ U := by rw [← Measure.map_apply (by fun_prop) hU.measurableSet, hinv q hqD]
  letI : (μ.map (fun x => x + h)).Regular :=
    Measure.Regular.map (μ := μ) (Homeomorph.addRight h)
  apply Measure.OuterRegular.ext_isOpen
  intro U hU
  rw [Measure.map_apply (by fun_prop) hU.measurableSet]
  apply le_antisymm (hle h U hU)
  have he := hle (-h) ((fun x : G => x + h) ⁻¹' U)
    (hU.preimage (show Continuous (fun x : G => x + h) from by fun_prop))
  have hpre : (fun x : G => x + -h) ⁻¹' ((fun x : G => x + h) ⁻¹' U) = U := by
    ext x
    simp [add_assoc]
  rw [hpre] at he
  exact he

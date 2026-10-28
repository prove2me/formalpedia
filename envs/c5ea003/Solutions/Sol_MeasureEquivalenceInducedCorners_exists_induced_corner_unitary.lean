-- Prove2me | solution 1 for MeasureEquivalenceInducedCorners.exists_induced_corner_unitary
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:32:04.417989+00:00
-- url     : https://prove2.me/submissions/15a0d850-184a-4a4c-870b-32556dc34200

import Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
import Definitions.Def_BenchmarkOperator20261026_InducedCornerUnitary
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryMultipliers
import Definitions.Def_BenchmarkOperator20261026_PiecewiseMeasureTransport
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Theorems.Thm_MeasureEquivalenceInducedCorners_exists_induced_corner_transport

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

-- Preserved source skeleton: InducedCornerUnitary
section
/-! Actual multiplication and group-shift unitaries on the induced L2
corner modules, and their simultaneous intertwining for equal finite mass. -/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace MeasureEquivalenceInducedCorners

open MeasureEquivalenceEquidecomposition MeasureUnitary

noncomputable section

variable {G Z : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Z] [MulAction G Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) [SigmaFinite μ]



omit [SigmaFinite μ] in
theorem inducedPhaseUnitary_coe (A : Set Z) (f : Z → ℂ) (hf : Measurable f)
    (hnorm : ∀ z, ‖f z‖ = 1) (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)) :
    inducedPhaseUnitary μ A f hf hnorm u =ᵐ[cornerMeasure (G := G) μ A]
      (fun p => f (orbitPoint p) • u p) :=
  phaseMap_coe (cornerMeasure (G := G) μ A) (fun p => f (orbitPoint p))
    (hf.comp orbitPoint_measurable) (fun p => hnorm (orbitPoint p)) u



omit [MulAction G Z] [MeasurableConstSMul G Z] in
theorem inducedShiftUnitary_coe (A : Set Z) (h : G)
    (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)) :
    inducedShiftUnitary μ A h u =ᵐ[cornerMeasure (G := G) μ A]
      (fun p => u (indexShift h⁻¹ p)) :=
  Lp.coeFn_compMeasurePreserving u (indexShift_preserving μ A h⁻¹)







variable (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)



end
end MeasureEquivalenceInducedCorners

end

/-! Actual multiplication and group-shift unitaries on the induced L2
corner modules, and their simultaneous intertwining for equal finite mass. -/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace MeasureEquivalenceInducedCorners
end MeasureEquivalenceInducedCorners
open MeasureEquivalenceInducedCorners
open MeasureEquivalenceEquidecomposition MeasureUnitary
variable {G Z : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Z] [MulAction G Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) [SigmaFinite μ]
variable (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)

include hmp

theorem solution
    (herg : ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (A B : Set Z) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfin : μ A ≠ ∞) (hmass : μ A = μ B) :
    ∃ U : Lp ℂ 2 (cornerMeasure (G := G) μ B) ≃ₗᵢ[ℂ] Lp ℂ 2 (cornerMeasure (G := G) μ A),
      (∀ (f : Z → ℂ) (hf : Measurable f) (hnorm : ∀ z, ‖f z‖ = 1)
        (u : Lp ℂ 2 (cornerMeasure (G := G) μ B)),
        U (inducedPhaseUnitary μ B f hf hnorm u) =
          inducedPhaseUnitary μ A f hf hnorm (U u)) ∧
      (∀ (h : G) (u : Lp ℂ 2 (cornerMeasure (G := G) μ B)),
        U (inducedShiftUnitary μ B h u) = inducedShiftUnitary μ A h (U u)) := by
  obtain ⟨F,H,hF,hH,hHF,_hFH,horbit,hcomm⟩ :=
    exists_induced_corner_transport μ hmp herg A B hA hB hfin hmass
  let U := pullbackUnitary (cornerMeasure (G := G) μ A) (cornerMeasure (G := G) μ B) F H hF hH hHF
  have hU (u : Lp ℂ 2 (cornerMeasure (G := G) μ B)) :
      U u =ᵐ[cornerMeasure (G := G) μ A] (fun p => u (F p)) :=
    Lp.coeFn_compMeasurePreserving u hF
  refine ⟨U, ?_, ?_⟩
  · intro f hf hnorm u
    apply Lp.ext
    filter_upwards [hU (inducedPhaseUnitary μ B f hf hnorm u),
      hF.quasiMeasurePreserving.ae (inducedPhaseUnitary_coe μ B f hf hnorm u),
      inducedPhaseUnitary_coe μ A f hf hnorm (U u), hU u, horbit]
      with p hleft hBphase hright hUp horbitp
    rw [hleft, hBphase, hright, hUp, horbitp]
  · intro h u
    apply Lp.ext
    filter_upwards [hU (inducedShiftUnitary μ B h u),
      hF.quasiMeasurePreserving.ae (inducedShiftUnitary_coe μ B h u),
      inducedShiftUnitary_coe μ A h (U u),
      (indexShift_preserving μ A h⁻¹).quasiMeasurePreserving.ae (hU u), hcomm h⁻¹]
      with p hleft hBshift hright hUp hcommp
    rw [hleft, hBshift, hright, hUp, hcommp]

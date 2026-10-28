-- Prove2me | solution 1 for MeasureEquivalenceMarkov.completedCoupling_ae_equal_iff
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:21:19.636206+00:00
-- url     : https://prove2.me/submissions/f9e8324d-4d27-4d67-9092-27dc0b10bece

import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Tactic

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

/-! Explicit stationary couplings from overlap measures along a
measurable automorphism. Their edges detect invariance. -/
open MeasureTheory Filter
open scoped ENNReal
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
open MeasureEquivalenceMarkov
variable {Z : Type*} [MeasurableSpace Z]

theorem solution
    (μ ν : Measure Z) (e : Z ≃ᵐ Z)
    (hνμ : ν ≪ μ) (hμν : μ ≪ ν)
    (f : Z → ℝ) (hf : Measurable f) :
    (∀ᵐ z ∂completedCoupling μ ν e, f z.1 = f z.2) ↔
      ∀ᵐ z ∂μ, f z = f (e.symm z) := by
  let A := acceptedEdges ν e
  let R := (μ + μ) - (ν + ν.map e.symm)
  have hgraph : Measurable (fun z : Z => (z, e.symm z)) :=
    measurable_id.prodMk e.symm.measurable
  have hdiag : Measurable (fun z : Z => (z,z)) := measurable_id.prodMk measurable_id
  have hpred : MeasurableSet {z : Z × Z | f z.1 = f z.2} :=
    measurableSet_eq_fun (hf.comp measurable_fst) (hf.comp measurable_snd)
  constructor
  · intro h
    have hAle : A ≤ completedCoupling μ ν e := by
      exact (Measure.le_add_right (le_refl A)).trans (Measure.le_add_right le_rfl)
    have hA := hAle.absolutelyContinuous.ae_le h
    exact hμν.ae_le (ae_of_ae_map hgraph.aemeasurable hA)
  · intro h
    have hA : ∀ᵐ z ∂A, f z.1 = f z.2 :=
      (ae_map_iff hgraph.aemeasurable hpred).mpr (hνμ.ae_le h)
    have hAS : ∀ᵐ z ∂A.map Prod.swap, f z.1 = f z.2 :=
      (ae_map_iff measurable_swap.aemeasurable hpred).mpr (hA.mono (fun _ hz => hz.symm))
    have hR : ∀ᵐ z ∂R.map (fun z => (z,z)), f z.1 = f z.2 :=
      (ae_map_iff hdiag.aemeasurable hpred).mpr (Eventually.of_forall (fun _ => rfl))
    exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr ⟨hA, hAS⟩, hR⟩

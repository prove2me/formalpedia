-- Prove2me | solution 1 for MeasureEquivalenceRestrictedProduct.head_event_zeroSum_invariant
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:37:34.704685+00:00
-- url     : https://prove2.me/submissions/f6ba20aa-b608-44e8-8e50-35edbb61a729

import Definitions.Def_BenchmarkOperator20261026_RestrictedAction
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedCorrection
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Instances.Rat
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_finite_volume_ac_exponential

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

-- Preserved source skeleton: RestrictedCorrection
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct



theorem headFinsupp_head (N : ℕ) (q : Fin N → ℚ) (i : Fin N) :
    headFinsupp N q i = q i := by
  classical
  simp [headFinsupp, Finsupp.finset_sum_apply, Finsupp.single_apply, Fin.val_inj]

theorem headFinsupp_tail (N : ℕ) (q : Fin N → ℚ) (k : ℕ) (hk : N ≤ k) :
    headFinsupp N q k = 0 := by
  classical
  simp only [headFinsupp, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finsupp.single_eq_of_ne
  omega

theorem rationalTotal_single (k : ℕ) (q : ℚ) : rationalTotal (Finsupp.single k q) = q :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem rationalTotal_headFinsupp (N : ℕ) (q : Fin N → ℚ) :
    rationalTotal (headFinsupp N q) = ∑ i : Fin N, q i := by
  simp [headFinsupp, map_sum, rationalTotal_single]











end MeasureEquivalenceRestrictedProduct

end

open MeasureTheory Set Filter
open scoped ENNReal
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct

theorem solution (N : ℕ)
    (E : Set RealSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : rationalZeroSumGroup,
      (rationalTranslation q) ⁻¹' E =ᵐ[restrictedProductMeasure] E)
    (r : Fin N → ℚ) (hr : (∑ i, r i) = 0) :
    (fun z : (Fin N → ℝ) × RealSequences =>
      (z.1 + fun i => (r i : ℝ), z.2)) ⁻¹' ((headTailEquiv N).symm ⁻¹' E)
      =ᵐ[(volume : Measure (Fin N → ℝ)).prod tailProbability]
        (headTailEquiv N).symm ⁻¹' E := by
  let q : rationalZeroSumGroup := ⟨headFinsupp N r, by
    change rationalTotal (headFinsupp N r) = 0
    rw [rationalTotal_headFinsupp, hr]⟩
  have hstage : stageMeasure N ≪ restrictedProductMeasure := by
    rw [← restrictedProductMeasure_restrict N]
    exact Measure.restrict_le_self.absolutelyContinuous
  have hm : MeasurePreserving (headTailEquiv N).symm
      ((Measure.pi (fun _ : Fin N => exponentialMeasure)).prod tailProbability) (stageMeasure N) :=
    ⟨(headTailEquiv N).symm.measurable, rfl⟩
  have hh := hm.quasiMeasurePreserving.ae_eq (hstage.ae_eq (hinv q))
  have hzero : ∀ᵐ z ∂(Measure.pi (fun _ : Fin N => exponentialMeasure)).prod tailProbability,
      E ((headTailEquiv N).symm (z.1 + fun i => (r i : ℝ), z.2)) =
        E ((headTailEquiv N).symm z) := by
    filter_upwards [hh] with z hz
    change E (rationalTranslation q ((headTailEquiv N).symm z)) =
      E ((headTailEquiv N).symm z) at hz
    have he : rationalTranslation q ((headTailEquiv N).symm z) =
        (headTailEquiv N).symm (z.1 + fun i => (r i : ℝ), z.2) := by
      apply (headTailEquiv N).injective
      apply Prod.ext
      · funext i
        simp only [headTailEquiv_head, rationalTranslation, Pi.add_apply,
          rationalRealShift, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          headTailEquiv_symm_head, MeasurableEquiv.apply_symm_apply]
        exact congrArg (fun a : ℚ => z.1 i + (a : ℝ)) (headFinsupp_head N r i)
      · funext k
        simp only [headTailEquiv_tail, rationalTranslation, Pi.add_apply,
          rationalRealShift, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          headTailEquiv_symm_tail, MeasurableEquiv.apply_symm_apply]
        have heq := headFinsupp_tail N r (N + k) (by omega)
        change z.2 k + (headFinsupp N r (N + k) : ℝ) = z.2 k
        rw [heq, Rat.cast_zero, add_zero]
    rw [he] at hz
    exact hz
  exact ((finite_volume_ac_exponential N).prod Measure.AbsolutelyContinuous.rfl).ae_eq hzero

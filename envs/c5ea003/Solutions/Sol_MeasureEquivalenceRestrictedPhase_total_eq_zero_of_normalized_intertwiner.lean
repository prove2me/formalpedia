-- Prove2me | solution 1 for MeasureEquivalenceRestrictedPhase.total_eq_zero_of_normalized_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:59:18.563475+00:00
-- url     : https://prove2.me/submissions/95ebf627-7a20-4fd5-bb75-12e464109459

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
import Definitions.Def_BenchmarkOperator20261026_InducedCornerUnitary
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorDenseFamily
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureL2Constants
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_RestrictedAction
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompactMeasure
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedInducedFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedInducedTuple
import Definitions.Def_BenchmarkOperator20261026_RestrictedModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedPhaseFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Definitions.Def_BenchmarkOperator20261026_RestrictedTranslatedCorner
import Definitions.Def_BenchmarkOperator20261026_RestrictedTranslationIntertwining
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
import Definitions.Def_BenchmarkOperator20261026_VectorSpectralState
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Theorems.Thm_MeasureEquivalenceRestrictedPhase_induced_corner_character_mass_eq
import Theorems.Thm_MeasureEquivalenceRestrictedPhase_normalizedTranslation_phase_intertwines
import Theorems.Thm_MeasureEquivalenceRestrictedPhase_translatedCorner_mass_eq_base_iff

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

-- Preserved source skeleton: RestrictedCompatibility
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct





































theorem restrictedProductMeasure_base : restrictedProductMeasure (stageSet 0) = 1 := by
  have he := congrArg (fun μ : Measure RealSequences => μ univ)
    (restrictedProductMeasure_restrict 0)
  dsimp only at he
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, stageMeasure_zero,
    measure_univ] at he
  exact he







end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: RestrictedInducedTuple
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid
open MeasureEquivalenceInducedCorners MeasureUnitary















theorem generatorEnumeration_surjective : Function.Surjective generatorEnumeration :=
  Classical.choose_spec (exists_surjective_nat Generator)







theorem intertwines_generators_of_intertwines_tuple (k l : CompactSequences)
    (W : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hW : ∀ n u, W (inducedTuple k n u) = inducedTuple l n (W u)) :
    (∀ i u, W (inducedFamilyPhase k i u) = inducedFamilyPhase l i (W u)) ∧
      (∀ q u, W (inducedFamilyShift q u) = inducedFamilyShift q (W u)) := by
  constructor
  · intro i u
    obtain ⟨n, hn⟩ := generatorEnumeration_surjective (Sum.inl i)
    have hh := hW n u
    simpa only [inducedTuple, inducedGenerator, hn, Sum.elim_inl] using hh
  · intro q u
    obtain ⟨n, hn⟩ := generatorEnumeration_surjective (Sum.inr q)
    have hh := hW n u
    simpa only [inducedTuple, inducedGenerator, hn, Sum.elim_inr] using hh

end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: RestrictedTranslatedCorner
section
/-! The exact translated finite corner and the measure-preserving map
to the scalar multiple dictated by the restricted-product modulus. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners MeasureEquivalenceEquidecomposition







theorem translatedCorner_measurable (h : RealSequences) : MeasurableSet (translatedCorner h) :=
  (measurable_id.add_const h) (measurable_stageSet 0)

theorem translatedCorner_mass (h : RealSequences) (hs : Summable (fun n => |h n|)) :
    restrictedProductMeasure (translatedCorner h) = (translationScale h : ℝ≥0∞) := by
  have hm := congrArg (fun M : Measure RealSequences => M (stageSet 0))
    (map_summable_restrictedProductMeasure h hs)
  change (restrictedProductMeasure.map (fun x : RealSequences => x + h)) (stageSet 0) =
    (ENNReal.ofReal (Real.exp (∑' n, h n)) • restrictedProductMeasure) (stageSet 0) at hm
  rw [Measure.map_apply (by fun_prop : Measurable (fun x : RealSequences => x + h))
    (measurable_stageSet 0), Measure.smul_apply, restrictedProductMeasure_base,
    smul_eq_mul, mul_one] at hm
  exact hm.trans (ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le)

theorem translatedCorner_finite (h : RealSequences) (hs : Summable (fun n => |h n|)) :
    restrictedProductMeasure (translatedCorner h) ≠ ∞ := by
  rw [translatedCorner_mass h hs]
  exact ENNReal.coe_ne_top







theorem translatedCorner_quasiMeasurePreserving (h : RealSequences)
    (hs : Summable (fun n => |h n|)) :
    Measure.QuasiMeasurePreserving (translatedCornerEquiv h)
      (cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h))
      (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)) := by
  refine ⟨(translatedCornerEquiv h).measurable, ?_⟩
  rw [(translatedCorner_preserving h hs).map_eq]
  exact Measure.smul_absolutelyContinuous





end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: RestrictedTranslationIntertwining
section
/-! A scalar-normalized translation intertwines the actual phase and
index-shift generators on the translated corner. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners







theorem normalizedTranslation_shift_intertwines (h : RealSequences)
    (hs : Summable (fun n => |h n|))
    (V : InducedHilbert ≃ₗᵢ[ℂ] TranslatedHilbert h) (a : ℝ)
    (hV : ∀ u : InducedHilbert,
      V u =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h)]
        fun p => a • u (translatedCornerEquiv h p))
    (g : RationalGroup) (u : InducedHilbert) :
    V (inducedFamilyShift g u) =
      inducedShiftUnitary restrictedProductMeasure (translatedCorner h) g (V u) := by
  apply Lp.ext
  filter_upwards [hV (inducedFamilyShift g u),
    (translatedCorner_quasiMeasurePreserving h hs).ae
      (inducedShiftUnitary_coe restrictedProductMeasure (stageSet 0) g u),
    inducedShiftUnitary_coe restrictedProductMeasure (translatedCorner h) g (V u),
    (indexShift_preserving restrictedProductMeasure (translatedCorner h) g⁻¹).quasiMeasurePreserving.ae (hV u)]
      with p hleft hinside hright hVp
  rw [hleft, hright, hVp]
  exact congrArg (fun z : ℂ => a • z) hinside

end MeasureEquivalenceRestrictedPhase

end

/-! The finite-corner mass invariant detects the total of a summable
parameter translation. The normalization unitary is supplied explicitly
with its actual scalar pullback formula. -/
open MeasureTheory Filter Set
open scoped ENNReal NNReal
set_option maxHeartbeats 1500000
namespace MeasureEquivalenceRestrictedPhase
end MeasureEquivalenceRestrictedPhase
open MeasureEquivalenceRestrictedPhase
open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners

theorem solution (h : RealSequences)
    (hs : Summable (fun n => |h n|)) (k l : CompactSequences)
    (he : k + sequenceEmbedding h = l)
    (W : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hW : ∀ n u, W (inducedTuple k n u) = inducedTuple l n (W u))
    (V : InducedHilbert ≃ₗᵢ[ℂ] TranslatedHilbert h) (a : ℝ)
    (hV : ∀ u : InducedHilbert,
      V u =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h)]
        fun p => a • u (translatedCornerEquiv h p)) :
    (∑' n, h n) = 0 := by
  let Q := V.symm.trans W
  have hgen := intertwines_generators_of_intertwines_tuple k l W hW
  have hphase (i : CharacterIndex) (u : InducedHilbert) :
      V (inducedFamilyPhase k i u) =
        inducedPhaseUnitary restrictedProductMeasure (translatedCorner h)
          (ambientPhase l i) (ambientPhase_measurable _ _) (ambientPhase_norm _ _) (V u) := by
    simpa only [he] using normalizedTranslation_phase_intertwines h hs V a hV k i u
  have hshift (g : RationalGroup) (u : InducedHilbert) :
      V (inducedFamilyShift g u) =
        inducedShiftUnitary restrictedProductMeasure (translatedCorner h) g (V u) :=
    normalizedTranslation_shift_intertwines h hs V a hV g u
  have hQphase (i : CharacterIndex) (f : TranslatedHilbert h) :
      Q (inducedPhaseUnitary restrictedProductMeasure (translatedCorner h)
        (ambientPhase l i) (ambientPhase_measurable _ _) (ambientPhase_norm _ _) f) =
        inducedFamilyPhase l i (Q f) := by
    have hinv : V.symm (inducedPhaseUnitary restrictedProductMeasure (translatedCorner h)
        (ambientPhase l i) (ambientPhase_measurable _ _) (ambientPhase_norm _ _) f) =
        inducedFamilyPhase k i (V.symm f) := by
      apply V.injective
      simpa only [LinearIsometryEquiv.apply_symm_apply] using (hphase i (V.symm f)).symm
    change W (V.symm _) = inducedFamilyPhase l i (W (V.symm f))
    rw [hinv, hgen.1]
  have hQshift (g : RationalGroup) (f : TranslatedHilbert h) :
      Q (inducedShiftUnitary restrictedProductMeasure (translatedCorner h) g f) =
        inducedFamilyShift g (Q f) := by
    have hinv : V.symm (inducedShiftUnitary restrictedProductMeasure (translatedCorner h) g f) =
        inducedFamilyShift g (V.symm f) := by
      apply V.injective
      simpa only [LinearIsometryEquiv.apply_symm_apply] using (hshift g (V.symm f)).symm
    change W (V.symm _) = inducedFamilyShift g (W (V.symm f))
    rw [hinv, hgen.2]
  have hfinS : restrictedProductMeasure (stageSet 0) ≠ ∞ := by
    rw [restrictedProductMeasure_base]
    exact ENNReal.one_ne_top
  have hm := induced_corner_character_mass_eq l (translatedCorner h) (stageSet 0)
    (translatedCorner_measurable h) (measurable_stageSet 0) (translatedCorner_finite h hs)
    hfinS Q hQphase hQshift
  exact (translatedCorner_mass_eq_base_iff h hs).mp hm

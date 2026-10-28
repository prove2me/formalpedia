-- Prove2me | solution 1 for MeasureEquivalenceRestrictedPhase.exists_induced_H_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:41:36.499829+00:00
-- url     : https://prove2.me/submissions/6c6f58f0-ba60-4bb9-b4f3-e11e652f6905

import Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
import Definitions.Def_BenchmarkOperator20261026_InducedCornerUnitary
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryMultipliers
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_PiecewiseMeasureTransport
import Definitions.Def_BenchmarkOperator20261026_RestrictedAction
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompactMeasure
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedErgodic
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedInducedFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedPermutation
import Definitions.Def_BenchmarkOperator20261026_RestrictedPhaseFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Theorems.Thm_MeasureEquivalenceInducedCorners_exists_induced_corner_unitary
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_finite_exponential_ac_volume
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_finite_permutation_invariant_of_zeroSum_invariant
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_head_event_zeroSum_invariant
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_null_of_invariant_and_base_null
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_tailProbability_zero_one_of_blockSwap_invariant

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

-- Preserved source skeleton: RestrictedAction
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct



theorem rationalTotal_eq_sum (q : ℕ →₀ ℚ) :
    rationalTotal q = q.sum (fun _ a => a) := by
  exact Finsupp.liftAddHom_apply _ _







theorem summable_abs_rationalRealShift (q : ℕ →₀ ℚ) :
    Summable (fun k => |rationalRealShift q k|) := by
  exact summable_of_hasFiniteSupport
    (q.hasFiniteSupport.fun_comp (g := fun a : ℚ => |(a : ℝ)|) (by simp))

theorem tsum_rationalRealShift (q : ℕ →₀ ℚ) :
    (∑' k, rationalRealShift q k) = (rationalTotal q : ℝ) := by
  rw [tsum_eq_sum (s := q.support) (fun k hk => by
    change (q k : ℝ) = 0
    rw [Finsupp.notMem_support_iff.mp hk, Rat.cast_zero])]
  rw [rationalTotal_eq_sum]
  change (∑ k ∈ q.support, (q k : ℝ)) = ((∑ k ∈ q.support, q k : ℚ) : ℝ)
  norm_cast



theorem measurePreserving_rationalTranslation (q : rationalZeroSumGroup) :
    MeasurePreserving (rationalTranslation q) restrictedProductMeasure restrictedProductMeasure := by
  constructor
  · exact measurable_id.add_const _
  · have he := map_summable_restrictedProductMeasure (rationalRealShift q)
      (summable_abs_rationalRealShift q)
    rw [tsum_rationalRealShift, show rationalTotal (q : ℕ →₀ ℚ) = 0 from q.property,
      Rat.cast_zero, Real.exp_zero, ENNReal.ofReal_one, one_smul] at he
    exact he





end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: RestrictedPermutation
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct









theorem blockSwap_large (N k : ℕ) (hk : 2 * N ≤ k) : blockSwap N k = k := by
  change blockSwapFun N k = k
  unfold blockSwapFun
  rw [if_neg (by omega), if_neg (not_lt.mpr hk)]













end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: RestrictedPropagation
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct







theorem null_or_conull_of_invariant_and_base_zero_one
    (E : Set RealSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : rationalZeroSumGroup,
      (rationalTranslation q) ⁻¹' E =ᵐ[restrictedProductMeasure] E)
    (hbase : tailProbability E = 0 ∨ tailProbability Eᶜ = 0) :
    restrictedProductMeasure E = 0 ∨ restrictedProductMeasure Eᶜ = 0 := by
  rcases hbase with h0 | h1
  · exact Or.inl (null_of_invariant_and_base_null E hE hinv h0)
  · apply Or.inr
    apply null_of_invariant_and_base_null Eᶜ hE.compl _ h1
    intro q
    simpa only [preimage_compl] using (hinv q).compl

end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: RestrictedErgodic
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct







theorem headTail_blockSwap (M : ℕ) (x : RealSequences) :
    headTailEquiv (2 * M + 1) (permute (blockSwap M) x) =
      (fun i => (headTailEquiv (2 * M + 1) x).1 (finBlockSwap M i),
        (headTailEquiv (2 * M + 1) x).2) := by
  apply Prod.ext
  · rfl
  · funext k
    change x (blockSwap M (2 * M + 1 + k)) = x (2 * M + 1 + k)
    rw [blockSwap_large M _ (by omega)]

theorem blockSwap_base_invariant_of_rational_invariant
    (E : Set RealSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : rationalZeroSumGroup,
      (rationalTranslation q) ⁻¹' E =ᵐ[restrictedProductMeasure] E) (M : ℕ) :
    (permute (blockSwap M)) ⁻¹' E =ᵐ[tailProbability] E := by
  let N := 2 * M + 1
  let F := (headTailEquiv N).symm ⁻¹' E
  have hF : MeasurableSet F := (headTailEquiv N).symm.measurable hE
  have hp := finite_permutation_invariant_of_zeroSum_invariant tailProbability (2 * M)
    F hF (head_event_zeroSum_invariant N E hE hinv) (finBlockSwap M)
  have hp' := ((finite_exponential_ac_volume N).prod Measure.AbsolutelyContinuous.rfl).ae_eq hp
  have hm : MeasurePreserving (headTailEquiv N).symm
      ((Measure.pi (fun _ : Fin N => exponentialMeasure)).prod tailProbability) (stageMeasure N) :=
    ⟨(headTailEquiv N).symm.measurable, rfl⟩
  have hh := (hm.symm (headTailEquiv N).symm).quasiMeasurePreserving.ae_eq hp'
  have hs : (permute (blockSwap M)) ⁻¹' E =ᵐ[stageMeasure N] E := by
    filter_upwards [hh] with x hx
    change E ((headTailEquiv N).symm
      ((fun i => (headTailEquiv N x).1 (finBlockSwap M i)), (headTailEquiv N x).2)) =
        E ((headTailEquiv N).symm (headTailEquiv N x)) at hx
    rw [← headTail_blockSwap M x, MeasurableEquiv.symm_apply_apply,
      MeasurableEquiv.symm_apply_apply] at hx
    exact hx
  have hbase : tailProbability ≪ stageMeasure N := by
    rw [← stageMeasure_restrict_base N]
    exact Measure.restrict_le_self.absolutelyContinuous
  exact hbase.ae_eq hs

theorem rationalZeroSum_ergodic
    (E : Set RealSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : rationalZeroSumGroup,
      (rationalTranslation q) ⁻¹' E =ᵐ[restrictedProductMeasure] E) :
    restrictedProductMeasure E = 0 ∨ restrictedProductMeasure Eᶜ = 0 := by
  apply null_or_conull_of_invariant_and_base_zero_one E hE hinv
  apply tailProbability_zero_one_of_blockSwap_invariant E hE
  exact blockSwap_base_invariant_of_rational_invariant E hE hinv

end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: RestrictedInducedFamily
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid
open MeasureEquivalenceInducedCorners MeasureEquivalenceEquidecomposition











theorem rational_smul_preserving (q : RationalGroup) :
    MeasurePreserving (fun x : RealSequences => q • x)
      restrictedProductMeasure restrictedProductMeasure :=
  measurePreserving_rationalTranslation (Multiplicative.toAdd q)

theorem rational_smul_ergodic (E : Set RealSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : RationalGroup, (fun x : RealSequences => q • x) ⁻¹' E = E) :
    restrictedProductMeasure E = 0 ∨ restrictedProductMeasure Eᶜ = 0 :=
  rationalZeroSum_ergodic E hE (fun q => Filter.EventuallyEq.of_eq (hinv (Multiplicative.ofAdd q)))

















end MeasureEquivalenceRestrictedPhase

end

open MeasureTheory Set Filter
open scoped ENNReal
namespace MeasureEquivalenceRestrictedPhase
end MeasureEquivalenceRestrictedPhase
open MeasureEquivalenceRestrictedPhase
open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid
open MeasureEquivalenceInducedCorners MeasureEquivalenceEquidecomposition

theorem solution (h : RealSequences)
    (hs : Summable (fun n => |h n|)) (hzero : (∑' n, h n) = 0) (k : CompactSequences) :
    ∃ W : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert,
      (∀ i u, W (inducedFamilyPhase k i u) = inducedFamilyPhase (k + sequenceEmbedding h) i (W u)) ∧
      (∀ q u, W (inducedFamilyShift q u) = inducedFamilyShift q (W u)) := by
  let B := stageSet 0
  let A := (fun x : RealSequences => x + h) ⁻¹' B
  have hB : MeasurableSet B := measurable_stageSet 0
  have hA : MeasurableSet A := (measurable_id.add_const h) hB
  let e := MeasurableEquiv.addRight h
  have he : MeasurePreserving e restrictedProductMeasure restrictedProductMeasure := by
    refine ⟨e.measurable, ?_⟩
    change restrictedProductMeasure.map (fun x => x + h) = restrictedProductMeasure
    rw [map_summable_restrictedProductMeasure h hs, hzero, Real.exp_zero,
      ENNReal.ofReal_one, one_smul]
  have hmA : restrictedProductMeasure A = restrictedProductMeasure B := by
    exact he.measure_preimage hB.nullMeasurableSet
  have hfin : restrictedProductMeasure B ≠ ∞ := by
    change restrictedProductMeasure (stageSet 0) ≠ ∞
    rw [restrictedProductMeasure_base]
    exact ENNReal.one_ne_top
  obtain ⟨U, hUphase, hUshift⟩ := exists_induced_corner_unitary restrictedProductMeasure
    rational_smul_preserving rational_smul_ergodic B A hB hA hfin hmA.symm
  let F := e.prodCongr (MeasurableEquiv.refl RationalGroup)
  have hF : MeasurePreserving F
      (cornerMeasure (G := RationalGroup) restrictedProductMeasure A)
      (cornerMeasure (G := RationalGroup) restrictedProductMeasure B) :=
    (he.restrict_preimage_emb e.measurableEmbedding B).prod (MeasurePreserving.id Measure.count)
  let V := pullbackUnitary
    (cornerMeasure (G := RationalGroup) restrictedProductMeasure A)
    (cornerMeasure (G := RationalGroup) restrictedProductMeasure B)
    F F.symm hF (hF.symm F) (ae_of_all _ F.symm_apply_apply)
  have hV (u : InducedHilbert) :
      V u =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure A]
        (fun p => u (F p)) := Lp.coeFn_compMeasurePreserving u hF
  refine ⟨V.trans U, ?_, ?_⟩
  · intro i u
    change U (V (inducedFamilyPhase k i u)) =
      inducedPhaseUnitary restrictedProductMeasure B (ambientPhase (k + sequenceEmbedding h) i)
        (ambientPhase_measurable _ _) (ambientPhase_norm _ _) (U (V u))
    rw [← hUphase (ambientPhase (k + sequenceEmbedding h) i)
      (ambientPhase_measurable _ _) (ambientPhase_norm _ _) (V u)]
    congr 1
    apply Lp.ext
    filter_upwards [hV (inducedFamilyPhase k i u),
      hF.quasiMeasurePreserving.ae (inducedPhaseUnitary_coe restrictedProductMeasure B
        (ambientPhase k i) (ambientPhase_measurable _ _) (ambientPhase_norm _ _) u),
      inducedPhaseUnitary_coe restrictedProductMeasure A
        (ambientPhase (k + sequenceEmbedding h) i) (ambientPhase_measurable _ _)
        (ambientPhase_norm _ _) (V u), hV u] with p hleft hinside hright hVp
    rw [hleft]
    change (inducedPhaseUnitary restrictedProductMeasure B (ambientPhase k i)
      (ambientPhase_measurable _ _) (ambientPhase_norm _ _) u) (F p) = _
    rw [hinside, hright, hVp]
    congr 1
    change character i (k + sequenceEmbedding (p.1 + h +
      rationalRealShift (Multiplicative.toAdd p.2 : rationalZeroSumGroup))) =
      character i (k + sequenceEmbedding h + sequenceEmbedding (p.1 +
        rationalRealShift (Multiplicative.toAdd p.2 : rationalZeroSumGroup)))
    simp only [map_add]
    congr 1
    abel
  · intro q u
    change U (V (inducedFamilyShift q u)) =
      inducedShiftUnitary restrictedProductMeasure B q (U (V u))
    rw [← hUshift q (V u)]
    congr 1
    apply Lp.ext
    filter_upwards [hV (inducedFamilyShift q u),
      hF.quasiMeasurePreserving.ae (inducedShiftUnitary_coe restrictedProductMeasure B q u),
      inducedShiftUnitary_coe restrictedProductMeasure A q (V u),
      (indexShift_preserving restrictedProductMeasure A q⁻¹).quasiMeasurePreserving.ae (hV u)]
      with p hleft hinside hright hVp
    rw [hleft]
    change (inducedShiftUnitary restrictedProductMeasure B q u) (F p) = _
    rw [hinside, hright, hVp]
    rfl

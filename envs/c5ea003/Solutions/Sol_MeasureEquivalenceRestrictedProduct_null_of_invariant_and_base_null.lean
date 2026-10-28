-- Prove2me | solution 1 for MeasureEquivalenceRestrictedProduct.null_of_invariant_and_base_null
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:39:04.340151+00:00
-- url     : https://prove2.me/submissions/7a2f5f86-b2b0-4e85-8291-d20de45cf12b

import Definitions.Def_BenchmarkOperator20261026_RestrictedAction
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedSaturation
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.Rat
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_exists_zeroSum_shift_to_base

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

-- Preserved source skeleton: RestrictedDeparture
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct








theorem one_le_exponentialDensity {t : ℝ} (ht : t ∈ baseInterval) :
    (1 : ℝ≥0∞) ≤ exponentialDensity t := by
  have hle : 1 ≤ Real.exp (-t) := Real.one_le_exp_iff.mpr (neg_nonneg.mpr ht.2)
  exact_mod_cast ENNReal.ofReal_le_ofReal hle



theorem volume_restrict_le_baseMeasure : (volume : Measure ℝ).restrict baseInterval ≤ baseMeasure := by
  unfold baseMeasure exponentialMeasure
  rw [restrict_withDensity (show MeasurableSet baseInterval from measurableSet_Icc)]
  conv_lhs => rw [← withDensity_one (μ := volume.restrict baseInterval)]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem (show MeasurableSet baseInterval from measurableSet_Icc)] with t ht
  exact one_le_exponentialDensity ht













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

-- Preserved source skeleton: RestrictedSaturation
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct



theorem innerInterval_subset : innerInterval ⊆ baseInterval := by
  intro t ht
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor <;> dsimp [innerInterval] at ht <;> linarith [ht.1, ht.2]

theorem baseMeasure_innerInterval_pos : 0 < baseMeasure innerInterval := by
  have hvol : 0 < volume innerInterval := by
    rw [innerInterval, Real.volume_Icc]
    apply ENNReal.ofReal_pos.mpr
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hle := volume_restrict_le_baseMeasure innerInterval
  rw [Measure.restrict_apply (show MeasurableSet innerInterval from measurableSet_Icc),
    Set.inter_eq_left.mpr innerInterval_subset] at hle
  exact hvol.trans_le hle

theorem tailProbability_ae_frequently_innerInterval :
    ∀ᵐ x ∂tailProbability, ∃ᶠ n in atTop, x n ∈ innerInterval := by
  let A : ℕ → Set RealSequences := fun n => {x | x n ∈ innerInterval}
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (measurable_pi_apply n) (show MeasurableSet innerInterval from measurableSet_Icc)
  have hA (n : ℕ) : tailProbability (A n) = baseMeasure innerInterval := by
    have hm : tailProbability.map (fun x => x n) = baseMeasure :=
      Measure.infinitePi_map_eval (fun _ : ℕ => baseMeasure) n
    change tailProbability ((fun x : RealSequences => x n) ⁻¹' innerInterval) = _
    rw [← Measure.map_apply (measurable_pi_apply n)
      (show MeasurableSet innerInterval from measurableSet_Icc), hm]
  have hi : ProbabilityTheory.iIndepSet A tailProbability := by
    apply (ProbabilityTheory.iIndepSet_iff_meas_biInter hAm).mpr
    intro s
    have he : (⋂ i ∈ s, A i) = Set.pi s (fun _ => innerInterval) := by
      ext x
      simp [A, Set.mem_pi]
    rw [he]
    change Measure.infinitePi (fun _ : ℕ => baseMeasure)
      (Set.pi s (fun _ => innerInterval)) = _
    rw [Measure.infinitePi_pi (fun _ : ℕ => baseMeasure)
      (fun _ _ => show MeasurableSet innerInterval from measurableSet_Icc)]
    exact Finset.prod_congr rfl (fun i _ => (hA i).symm)
  have hsum : (∑' n, tailProbability (A n)) = ∞ := by
    simp_rw [hA]
    exact ENNReal.tsum_const_eq_top_of_ne_zero baseMeasure_innerInterval_pos.ne'
  have hprob := ProbabilityTheory.measure_limsup_eq_one hAm hi hsum
  have hae : ∀ᵐ x ∂tailProbability, x ∈ limsup A atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hAm)).mpr hprob
  filter_upwards [hae] with x hx
  exact mem_limsup_iff_frequently_mem.mp hx

theorem measurable_frequently_innerInterval :
    MeasurableSet {x : RealSequences | ∃ᶠ n in atTop, x n ∈ innerInterval} := by
  have he : {x : RealSequences | ∃ᶠ n in atTop, x n ∈ innerInterval} =
      limsup (fun n => {x : RealSequences | x n ∈ innerInterval}) atTop := by
    ext x
    exact (mem_limsup_iff_frequently_mem (a := x)
      (s := fun n => {y : RealSequences | y n ∈ innerInterval}) (𝓕 := atTop)).symm
  rw [he]
  exact MeasurableSet.measurableSet_limsup (fun n =>
    (measurable_pi_apply n) (show MeasurableSet innerInterval from measurableSet_Icc))

theorem stageMeasure_ae_frequently_innerInterval (n : ℕ) :
    ∀ᵐ x ∂stageMeasure n, ∃ᶠ k in atTop, x k ∈ innerInterval := by
  unfold stageMeasure
  apply (ae_map_iff (headTailEquiv n).symm.measurable.aemeasurable
    measurable_frequently_innerInterval).mpr
  apply (Measure.ae_prod_iff_ae_ae
    ((headTailEquiv n).symm.measurable measurable_frequently_innerInterval)).mpr
  apply ae_of_all
  intro head
  filter_upwards [tailProbability_ae_frequently_innerInterval] with tail ht
  rw [frequently_atTop] at ht ⊢
  intro N
  obtain ⟨r, hr, hri⟩ := ht N
  refine ⟨n + r, by omega, ?_⟩
  simpa only [headTailEquiv_symm_tail] using hri

theorem restrictedProductMeasure_ae_frequently_innerInterval :
    ∀ᵐ x ∂restrictedProductMeasure, ∃ᶠ n in atTop, x n ∈ innerInterval := by
  rw [ae_iff]
  change restrictedProductStages.limit {x | ¬ ∃ᶠ n in atTop, x n ∈ innerInterval} = 0
  have hbad : MeasurableSet {x : RealSequences | ¬ ∃ᶠ n in atTop, x n ∈ innerInterval} :=
    measurable_frequently_innerInterval.compl
  rw [restrictedProductStages.limit_apply _ hbad]
  apply ENNReal.iSup_eq_zero.mpr
  intro n
  exact stageMeasure_ae_frequently_innerInterval n

end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: RestrictedPropagation
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem ae_exists_zeroSum_shift_to_base :
    ∀ᵐ x ∂restrictedProductMeasure,
      ∃ q : rationalZeroSumGroup, rationalTranslation q x ∈ stageSet 0 := by
  filter_upwards [restrictedProductStages.ae_mem_union,
    restrictedProductMeasure_ae_frequently_innerInterval] with x hx hf
  exact exists_zeroSum_shift_to_base x hx hf







end MeasureEquivalenceRestrictedProduct

end

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct

theorem solution (E : Set RealSequences) (hE : MeasurableSet E)
    (hinv : ∀ q : rationalZeroSumGroup,
      (rationalTranslation q) ⁻¹' E =ᵐ[restrictedProductMeasure] E)
    (hbase : tailProbability E = 0) : restrictedProductMeasure E = 0 := by
  have hzero : restrictedProductMeasure (E ∩ stageSet 0) = 0 := by
    rw [← Measure.restrict_apply hE, restrictedProductMeasure_restrict 0,
      stageMeasure_zero, hbase]
  have hS : ∀ᵐ x ∂restrictedProductMeasure, x ∈ stageSet 0 → x ∉ E := by
    rw [ae_iff]
    have he : {x | ¬ (x ∈ stageSet 0 → x ∉ E)} = E ∩ stageSet 0 := by
      ext x
      simp only [mem_setOf_eq, _root_.not_imp, not_not, mem_inter_iff, and_comm]
    rw [he]
    exact hzero
  have hq (q : rationalZeroSumGroup) : ∀ᵐ x ∂restrictedProductMeasure,
      rationalTranslation q x ∈ stageSet 0 → x ∉ E := by
    have hpull := (measurePreserving_rationalTranslation q).quasiMeasurePreserving.ae hS
    filter_upwards [hpull, (hinv q).mem_iff] with x hx he
    intro hs hxe
    exact hx hs (he.mpr hxe)
  have hall : ∀ᵐ x ∂restrictedProductMeasure,
      ∀ q : rationalZeroSumGroup, rationalTranslation q x ∈ stageSet 0 → x ∉ E :=
    ae_all_iff.mpr hq
  have hnot : ∀ᵐ x ∂restrictedProductMeasure, x ∉ E := by
    filter_upwards [hall, ae_exists_zeroSum_shift_to_base] with x hx hex
    obtain ⟨q, hq⟩ := hex
    exact hx q hq
  simpa only [ae_iff, not_not] using hnot

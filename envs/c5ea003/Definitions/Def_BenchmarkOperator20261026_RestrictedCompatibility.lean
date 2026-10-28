-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
-- name    : BenchmarkOperator20261026_RestrictedCompatibility
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:40:43.305051+00:00
-- url     : https://prove2.me/theorems/76180e31-09f5-46e3-9132-13c18d3b1e91
-- title:
--   Restricted Compatibility
-- statement:
--   Defines the finite shifts and shifted base sets, the compatible-stage package, the resulting restricted-product measure and its measurable carrier. The retained compatibility and finite-translation identities justify these definitions and their sigma-finite, non-atomic instances.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedCompatibility.lean, lines 11–180; source SHA-256 9a27a53c7dd9b8641833ce8f9edb77bad303af54b0ab3ff611b072d7585e3952. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.Rat

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
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem restrict_image_eq_of_same_modulus {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (e : α ≃ᵐ α) (s : Set α) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hμ : μ.map e = c • μ) (hν : ν.map e = c • ν)
    (hs : μ.restrict s = ν.restrict s) :
    μ.restrict (e '' s) = ν.restrict (e '' s) := by
  have ht (ξ : Measure α) (hξ : ξ.map e = c • ξ) :
      (ξ.restrict s).map e = c • ξ.restrict (e '' s) := by
    calc
      (ξ.restrict s).map e = (ξ.restrict (e ⁻¹' (e '' s))).map e := by
        rw [e.injective.preimage_image]
      _ = (ξ.map e).restrict (e '' s) := (e.restrict_map ξ (e '' s)).symm
      _ = c • ξ.restrict (e '' s) := by rw [hξ, Measure.restrict_smul]
  have he := congrArg (fun ξ : Measure α => ξ.map e) hs
  dsimp only at he
  rw [ht μ hμ, ht ν hν] at he
  ext t htm
  have hev := congrArg (fun ξ : Measure α => ξ t) he
  dsimp only at hev
  simp only [Measure.smul_apply, smul_eq_mul] at hev
  exact (ENNReal.mul_right_inj hc0 hct).mp hev

def finiteShift (n : ℕ) (q : Fin n → ℚ) (k : ℕ) : ℝ :=
  if hk : k < n then q ⟨k, hk⟩ else 0

@[simp] theorem finiteShift_head (n : ℕ) (q : Fin n → ℚ) (i : Fin n) :
    finiteShift n q i = (q i : ℝ) := by simp [finiteShift, i.is_lt]

theorem finiteShift_tail (n : ℕ) (q : Fin n → ℚ) (k : ℕ) (hk : n ≤ k) :
    finiteShift n q k = 0 := by simp [finiteShift, not_lt.mpr hk]

def shiftEquiv (h : RealSequences) : RealSequences ≃ᵐ RealSequences where
  toEquiv := Equiv.addRight h
  measurable_toFun := measurable_id.add_const h
  measurable_invFun := measurable_id.sub_const h

def shiftedBase (n : ℕ) (q : Fin n → ℚ) : Set RealSequences :=
  shiftEquiv (finiteShift n q) '' stageSet 0

theorem shiftedBase_subset_stage (n : ℕ) (q : Fin n → ℚ) :
    shiftedBase n q ⊆ stageSet n := by
  rintro x ⟨y, hy, rfl⟩ k hk
  change y k + finiteShift n q k ∈ baseInterval
  rw [finiteShift_tail n q k hk, add_zero]
  exact hy k (Nat.zero_le _)

theorem iUnion_shiftedBase (n : ℕ) : (⋃ q : Fin n → ℚ, shiftedBase n q) = stageSet n := by
  apply Subset.antisymm
  · exact iUnion_subset (shiftedBase_subset_stage n)
  · intro x hx
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hq (i : Fin n) : ∃ q : ℚ, x i < q ∧ (q : ℝ) < x i + Real.log 2 :=
      exists_rat_btwn (by linarith)
    choose q hqlo hqhi using hq
    apply mem_iUnion.mpr
    refine ⟨q, x - finiteShift n q, ?_, ?_⟩
    · intro k _
      change -Real.log 2 ≤ x k - finiteShift n q k ∧ x k - finiteShift n q k ≤ 0
      by_cases hk : k < n
      · rw [show finiteShift n q k = (q ⟨k, hk⟩ : ℝ) from finiteShift_head n q ⟨k, hk⟩]
        constructor <;> linarith [hqlo ⟨k, hk⟩, hqhi ⟨k, hk⟩]
      · rw [finiteShift_tail n q k (le_of_not_gt hk), sub_zero]
        exact hx k (le_of_not_gt hk)
    · change (x - finiteShift n q) + finiteShift n q = x
      exact sub_add_cancel _ _

theorem finiteShift_sum (n m : ℕ) (hnm : n ≤ m) (q : Fin n → ℚ) :
    (∑ i : Fin m, finiteShift n q i) = ∑ i : Fin n, (q i : ℝ) := by
  have hs : (∑ i : Fin n, finiteShift n q i) = ∑ i : Fin n, (q i : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    exact finiteShift_head n q i
  rw [← hs, Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hnm)
  intro k _ hk
  exact finiteShift_tail n q k (le_of_not_gt (by simpa using hk))

theorem map_finiteShift_stage (n m : ℕ) (hnm : n ≤ m) (q : Fin n → ℚ) :
    (stageMeasure m).map (shiftEquiv (finiteShift n q)) =
      ENNReal.ofReal (Real.exp (∑ i : Fin n, (q i : ℝ))) • stageMeasure m := by
  change (stageMeasure m).map (fun x => x + finiteShift n q) = _
  have he := map_add_stageMeasure m (finiteShift n q)
    (fun k hk => finiteShift_tail n q k (hnm.trans hk))
  rw [finiteShift_sum n m hnm q] at he
  exact he

theorem stageMeasure_compatible (n m : ℕ) (hnm : n ≤ m) :
    (stageMeasure m).restrict (stageSet n) = stageMeasure n := by
  rw [← stageMeasure_restrict_self n, ← iUnion_shiftedBase n]
  apply Measure.restrict_iUnion_congr.mpr
  intro q
  apply restrict_image_eq_of_same_modulus (stageMeasure m) (stageMeasure n)
    (shiftEquiv (finiteShift n q)) (stageSet 0)
    (ENNReal.ofReal (Real.exp (∑ i : Fin n, (q i : ℝ))))
  · exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  · exact ENNReal.ofReal_ne_top
  · exact map_finiteShift_stage n m hnm q
  · exact map_finiteShift_stage n n le_rfl q
  · rw [stageMeasure_restrict_base, stageMeasure_restrict_base]

def restrictedProductStages : CompatibleStages RealSequences where
  stage := stageSet
  measurable_stage := measurable_stageSet
  measure := stageMeasure
  compatible := stageMeasure_compatible

def restrictedProductMeasure : Measure RealSequences := restrictedProductStages.limit

def restrictedProductSpace : Set RealSequences := ⋃ n, stageSet n

theorem measurable_restrictedProductSpace : MeasurableSet restrictedProductSpace :=
  MeasurableSet.iUnion measurable_stageSet

theorem restrictedProductMeasure_restrict (n : ℕ) :
    restrictedProductMeasure.restrict (stageSet n) = stageMeasure n :=
  restrictedProductStages.limit_restrict n

instance _root_.MeasureEquivalenceRestrictedProduct.instSigmaFiniteRealSequencesRestrictedProductMeasure : SigmaFinite restrictedProductMeasure := by
  letI (n : ℕ) : SigmaFinite (restrictedProductStages.measure n) := by
    change SigmaFinite (stageMeasure n)
    infer_instance
  exact restrictedProductStages.sigmaFinite_limit





instance _root_.MeasureEquivalenceRestrictedProduct.instNoAtomsRealSequencesRestrictedProductMeasure : NoAtoms restrictedProductMeasure := by
  constructor
  intro x
  change restrictedProductStages.limit {x} = 0
  rw [restrictedProductStages.limit_apply _ (measurableSet_singleton x)]
  apply ENNReal.iSup_eq_zero.mpr
  intro n
  change stageMeasure n {x} = 0
  exact measure_singleton x



theorem map_finite_support_restrictedProductMeasure (h : RealSequences) (N : ℕ)
    (hh : ∀ k, N ≤ k → h k = 0) :
    restrictedProductMeasure.map (fun x => x + h) =
      ENNReal.ofReal (Real.exp (∑ k ∈ Finset.range N, h k)) • restrictedProductMeasure := by
  apply restrictedProductStages.map_limit_eq_smul (measurable_id.add_const h) _ N
  intro n hn
  change (stageMeasure n).map (fun x => x + h) = _
  rw [map_add_stageMeasure n h (fun k hk => hh k (hn.trans hk))]
  congr 2
  rw [Fin.sum_univ_eq_sum_range]
  symm
  congr 1
  apply Finset.sum_subset (Finset.range_mono hn)
  intro k _ hk
  exact hh k (le_of_not_gt (by simpa using hk))

end MeasureEquivalenceRestrictedProduct



-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
-- name    : BenchmarkOperator20261026_RestrictedProduct
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:38:55.308916+00:00
-- url     : https://prove2.me/theorems/206d493e-640c-4644-85ff-ff3333ee3813
-- title:
--   Restricted Product
-- statement:
--   Defines the increasing limit of measures and a compatible-stage package together with its limit measure. The retained evaluation, restriction, carrier and sigma-finiteness identities justify this measure-theoretic gluing construction.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedProduct.lean, lines 21–146; source SHA-256 a897729bbdf4addc460cda33f83ee961bd232419597815f0b3c3a4c8e61bfe1e. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

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

/-! Increasing compatible measures and their restricted-product limit.
This file supplies the measure-theoretic gluing step used in Section 11.
The concrete exponential-density finite stages are constructed separately.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

variable {α : Type*} [MeasurableSpace α]

theorem tsum_iSup_of_monotone (f : ℕ → ℕ → ℝ≥0∞)
    (hf : ∀ i, Monotone (fun n => f n i)) :
    (∑' i, ⨆ n, f n i) = ⨆ n, ∑' i, f n i := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  calc
    (⨆ s : Finset ℕ, ∑ i ∈ s, ⨆ n, f n i) =
        ⨆ s : Finset ℕ, ⨆ n, ∑ i ∈ s, f n i := by
      congr 1
      funext s
      exact ENNReal.finsetSum_iSup_of_monotone hf
    _ = ⨆ n, ⨆ s : Finset ℕ, ∑ i ∈ s, f n i := iSup_comm

def increasingLimit (μ : ℕ → Measure α) (hμ : Monotone μ) : Measure α :=
  Measure.ofMeasurable (fun s _ => ⨆ n, μ n s) (by simp) (by
    intro s hs hdisj
    simp_rw [measure_iUnion hdisj hs]
    exact (tsum_iSup_of_monotone (fun n i => μ n (s i))
      (fun i n m hnm => hμ hnm (s i))).symm)

theorem increasingLimit_apply (μ : ℕ → Measure α) (hμ : Monotone μ)
    (s : Set α) (hs : MeasurableSet s) :
    increasingLimit μ hμ s = ⨆ n, μ n s :=
  Measure.ofMeasurable_apply s hs

/-- Compatibility includes the fact that each measure is carried by its own stage. -/
structure CompatibleStages (α : Type*) [MeasurableSpace α] where
  stage : ℕ → Set α
  measurable_stage : ∀ n, MeasurableSet (stage n)
  measure : ℕ → Measure α
  compatible : ∀ n m, n ≤ m → (measure m).restrict (stage n) = measure n

namespace CompatibleStages

variable (S : CompatibleStages α)

theorem monotone_measure : Monotone S.measure := by
  intro n m hnm
  rw [← S.compatible n m hnm]
  exact Measure.restrict_le_self

def limit : Measure α := increasingLimit S.measure S.monotone_measure

theorem limit_apply (s : Set α) (hs : MeasurableSet s) :
    S.limit s = ⨆ n, S.measure n s := increasingLimit_apply _ _ s hs

theorem limit_restrict (n : ℕ) : S.limit.restrict (S.stage n) = S.measure n := by
  ext t ht
  rw [Measure.restrict_apply ht, S.limit_apply _ (ht.inter (S.measurable_stage n))]
  apply le_antisymm
  · apply iSup_le
    intro m
    have hle := S.monotone_measure (Nat.le_max_right n m) (t ∩ S.stage n)
    have he : S.measure (max n m) (t ∩ S.stage n) = S.measure n t := by
      rw [← Measure.restrict_apply ht, S.compatible n (max n m) (Nat.le_max_left _ _)]
    exact hle.trans he.le
  · have he : S.measure n (t ∩ S.stage n) = S.measure n t := by
      rw [← Measure.restrict_apply ht, S.compatible n n le_rfl]
    exact he.symm.le.trans (le_iSup (fun m => S.measure m (t ∩ S.stage n)) n)

theorem limit_compl_union : S.limit (⋃ n, S.stage n)ᶜ = 0 := by
  rw [S.limit_apply _ (MeasurableSet.iUnion S.measurable_stage).compl]
  apply ENNReal.iSup_eq_zero.mpr
  intro n
  have hn : S.measure n (S.stage n)ᶜ = 0 := by
    rw [← S.compatible n n le_rfl, Measure.restrict_apply (S.measurable_stage n).compl]
    simp
  exact measure_mono_null (compl_subset_compl.mpr (subset_iUnion S.stage n)) hn

theorem ae_mem_union : ∀ᵐ x ∂S.limit, x ∈ ⋃ n, S.stage n := by
  rw [ae_iff]
  exact S.limit_compl_union

theorem limit_eq_restrict_union : S.limit.restrict (⋃ n, S.stage n) = S.limit :=
  Measure.restrict_eq_self_of_ae_mem S.ae_mem_union

theorem sigmaFinite_limit [∀ n, SigmaFinite (S.measure n)] : SigmaFinite S.limit := by
  let E : ℕ → ℕ → Set α := fun n k =>
    (spanningSets (S.measure n) k ∩ S.stage n) ∪ (⋃ n, S.stage n)ᶜ
  let F : ℕ → Set α := fun i => E (Nat.unpair i).1 (Nat.unpair i).2
  have hfinite (n k : ℕ) : S.limit (E n k) < ∞ := by
    have hinter : S.limit (spanningSets (S.measure n) k ∩ S.stage n) =
        S.measure n (spanningSets (S.measure n) k) := by
      rw [← Measure.restrict_apply (measurableSet_spanningSets _ _), S.limit_restrict]
    have hle := measure_union_le (μ := S.limit)
      (spanningSets (S.measure n) k ∩ S.stage n) (⋃ n, S.stage n)ᶜ
    rw [hinter, S.limit_compl_union, add_zero] at hle
    exact hle.trans_lt (measure_spanningSets_lt_top (S.measure n) k)
  refine ⟨⟨{
    set := F
    set_mem := fun _ => trivial
    finite := fun i => hfinite (Nat.unpair i).1 (Nat.unpair i).2
    spanning := ?_ }⟩⟩
  apply eq_univ_iff_forall.mpr
  intro x
  by_cases hx : x ∈ ⋃ n, S.stage n
  · obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hs : x ∈ ⋃ k, spanningSets (S.measure n) k := by
      rw [iUnion_spanningSets]
      trivial
    obtain ⟨k, hk⟩ := mem_iUnion.mp hs
    apply mem_iUnion.mpr
    refine ⟨Nat.pair n k, ?_⟩
    dsimp only [F]
    rw [Nat.unpair_pair]
    exact Or.inl ⟨hk, hn⟩
  · apply mem_iUnion.mpr
    refine ⟨Nat.pair 0 0, ?_⟩
    dsimp only [F]
    rw [Nat.unpair_pair]
    exact Or.inr hx

/-- An eventual modulus identity at the finite stages passes to their increasing limit. -/
theorem map_limit_eq_smul {f : α → α} (hf : Measurable f) (c : ℝ≥0∞)
    (N : ℕ) (hmod : ∀ n, N ≤ n → (S.measure n).map f = c • S.measure n) :
    S.limit.map f = c • S.limit := by
  ext s hs
  rw [Measure.map_apply hf hs, S.limit_apply _ (hf hs), Measure.smul_apply,
    S.limit_apply _ hs, smul_eq_mul]
  have hm (t : Set α) : Monotone (fun n => S.measure n t) :=
    fun n m hnm => S.monotone_measure hnm t
  rw [← (hm (f ⁻¹' s)).iSup_nat_add N, ← (hm s).iSup_nat_add N]
  rw [ENNReal.mul_iSup]
  congr 1
  funext n
  have he := congrArg (fun μ : Measure α => μ s) (hmod (n + N) (Nat.le_add_left N n))
  simpa only [Measure.map_apply hf hs, Measure.smul_apply, smul_eq_mul] using he

end CompatibleStages

end MeasureEquivalenceRestrictedProduct



-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedBoxMass
-- name    : BenchmarkOperator20261026_RestrictedBoxMass
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:48:19.452797+00:00
-- url     : https://prove2.me/theorems/a504fa87-b2ec-49c1-a40a-10435a1d7ab1
-- title:
--   Restricted Box Mass
-- statement:
--   Defines finite base boxes and retains the corresponding shifted stage and restricted-product box-mass identities. These formulas are used in the later computation of the full translation modulus.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedBoxMass.lean, lines 10–94; source SHA-256 c7f24f486a0adfd0a0030bcd977c7db59fb308a01f620dd791b05f3a1fa5db68. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedMass
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
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
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

def baseBox (B : ℕ → Set ℝ) : Set RealSequences := Set.univ.pi B

theorem measurable_baseBox (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    MeasurableSet (baseBox B) := MeasurableSet.univ_pi hB

theorem fin_prod_tail_one (f : ℕ → ℝ≥0∞) (M N : ℕ) (hMN : M ≤ N)
    (hf : ∀ k, M ≤ k → f k = 1) :
    (∏ i : Fin N, f i) = ∏ i : Fin M, f i := by
  rw [Fin.prod_univ_eq_prod_range, Fin.prod_univ_eq_prod_range]
  symm
  apply Finset.prod_subset (Finset.range_mono hMN)
  intro k _ hk
  exact hf k (le_of_not_gt (by simpa using hk))

theorem shifted_stage_box_mass (h : RealSequences) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) (M N : ℕ) (hMN : M ≤ N)
    (hBtail : ∀ k, M ≤ k → B k = baseInterval) :
    ((stageMeasure N).map (fun x => x + h)) (baseBox B) =
      ENNReal.ofReal (Real.exp (∑ i : Fin N, h i)) *
        (∏ i : Fin M, exponentialMeasure (B i)) * tailStayProbability h N := by
  let H : Set (Fin N → ℝ) := Set.univ.pi (fun i => (fun t : ℝ => t + h i) ⁻¹' B i)
  have hpre : ((fun x : RealSequences => x + h) ∘ (headTailEquiv N).symm) ⁻¹'
      baseBox B = H ×ˢ tailStaySet h N := by
    ext z
    change (∀ k, k ∈ Set.univ → (headTailEquiv N).symm z k + h k ∈ B k) ↔
      ((∀ i : Fin N, i ∈ Set.univ → z.1 i + h i ∈ B i) ∧
        ∀ k, z.2 k + h (N + k) ∈ baseInterval)
    constructor
    · intro hz
      constructor
      · intro i _
        simpa only [headTailEquiv_symm_head] using hz (i : ℕ) (mem_univ _)
      · intro k
        have hh := hz (N + k) (mem_univ _)
        rw [hBtail (N + k) (hMN.trans (Nat.le_add_right _ _))] at hh
        simpa only [headTailEquiv_symm_tail] using hh
    · rintro ⟨hh, ht⟩ k _
      by_cases hk : k < N
      · rw [headTailEquiv_symm_head N z ⟨k, hk⟩]
        exact hh ⟨k, hk⟩ (mem_univ _)
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_gt hk)
        rw [hBtail (N + r) (hMN.trans (Nat.le_add_right _ _))]
        simpa only [headTailEquiv_symm_tail] using ht r
  unfold stageMeasure
  rw [Measure.map_map (by fun_prop) (headTailEquiv N).symm.measurable,
    Measure.map_apply (by fun_prop) (measurable_baseBox B hB), hpre, Measure.prod_prod]
  change (Measure.pi (fun _ : Fin N => exponentialMeasure)) H * tailStayProbability h N = _
  dsimp only [H]
  rw [Measure.pi_pi]
  simp_rw [exponentialMeasure_add_preimage _ _ (hB _)]
  rw [Finset.prod_mul_distrib, fin_prod_ofReal_exp]
  have hp := fin_prod_tail_one (fun k => exponentialMeasure (B k)) M N hMN
    (fun k hk => by dsimp only; rw [hBtail k hk, exponentialMeasure_baseInterval])
  rw [hp]

theorem shifted_restricted_box_mass (h : RealSequences)
    (hh : Summable (fun n => |h n|)) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) (M : ℕ)
    (hBtail : ∀ k, M ≤ k → B k = baseInterval) :
    (restrictedProductMeasure.map (fun x => x + h)) (baseBox B) =
      ENNReal.ofReal (Real.exp (∑' n, h n)) * ∏ i : Fin M, exponentialMeasure (B i) := by
  have hs : Summable h := summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using hh)
  have hscalar : Tendsto (fun N => ENNReal.ofReal (Real.exp (∑ k ∈ Finset.range N, h k)))
      atTop (𝓝 (ENNReal.ofReal (Real.exp (∑' n, h n)))) :=
    ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto _).comp hs.hasSum.tendsto_sum_nat)
  have hbase := ENNReal.Tendsto.mul hscalar
    (Or.inr (by norm_num : (1 : ℝ≥0∞) ≠ ∞)) (tendsto_tailStayProbability h hh)
    (Or.inl (by norm_num : (1 : ℝ≥0∞) ≠ 0))
  simp only [mul_one] at hbase
  have hprod := ENNReal.Tendsto.mul_const hbase
    (b := ∏ i : Fin M, exponentialMeasure (B i))
    (Or.inl (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
  rw [Measure.map_apply (by fun_prop) (measurable_baseBox B hB)]
  change restrictedProductStages.limit ((fun x : RealSequences => x + h) ⁻¹' baseBox B) = _
  rw [restrictedProductStages.limit_apply _
    ((show Measurable (fun x : RealSequences => x + h) from by fun_prop) (measurable_baseBox B hB))]
  apply iSup_eq_of_tendsto
  · intro n m hnm
    exact restrictedProductStages.monotone_measure hnm _
  · apply hprod.congr'
    filter_upwards [eventually_ge_atTop M] with N hN
    change _ = (stageMeasure N) ((fun x : RealSequences => x + h) ⁻¹' baseBox B)
    rw [← Measure.map_apply (by fun_prop) (measurable_baseBox B hB),
      shifted_stage_box_mass h B hB M N hN hBtail, Fin.sum_univ_eq_sum_range]
    ring

end MeasureEquivalenceRestrictedProduct



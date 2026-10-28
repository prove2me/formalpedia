-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedModulus
-- name    : BenchmarkOperator20261026_RestrictedModulus
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:49:04.106589+00:00
-- url     : https://prove2.me/theorems/f4c13487-200b-453e-abd5-a9a7c75760b1
-- title:
--   Restricted Modulus
-- statement:
--   Retains the shifted cylinder, restricted-base and full restricted-product measure formulas for finite and summable translations. In particular, these formulas express the exponential translation modulus under their stated hypotheses. They are used to compare finite-corner masses.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedModulus.lean, lines 10–152; source SHA-256 7a4fc98b029001fdf12be75a697b5f4e08ce494f2d2bd463398b72de8e916224. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_RestrictedBoxMass
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Definitions.Def_BenchmarkOperator20261026_RestrictedSupport
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

theorem shifted_restricted_cylinder_mass (h : RealSequences)
    (hh : Summable (fun n => |h n|)) (s : Finset ℕ) (t : ℕ → Set ℝ)
    (ht : ∀ i, MeasurableSet (t i)) :
    (restrictedProductMeasure.map (fun x => x + h)) (Set.pi s t ∩ stageSet 0) =
      ENNReal.ofReal (Real.exp (∑' n, h n)) * ∏ i ∈ s, baseMeasure (t i) := by
  let B : ℕ → Set ℝ := fun i => if i ∈ s then t i ∩ baseInterval else baseInterval
  let M : ℕ := s.sup id + 1
  have hsM : s ⊆ Finset.range M := by
    intro i hi
    have hle : i ≤ s.sup id := Finset.le_sup (f := id) hi
    exact Finset.mem_range.mpr (by dsimp [M]; omega)
  have hBm (i : ℕ) : MeasurableSet (B i) := by
    dsimp only [B]
    split_ifs
    · exact (ht i).inter (show MeasurableSet baseInterval from measurableSet_Icc)
    · exact measurableSet_Icc
  have hBtail (k : ℕ) (hk : M ≤ k) : B k = baseInterval := by
    have hnot : k ∉ s := by intro hks; have := Finset.mem_range.mp (hsM hks); omega
    simp only [B, if_neg hnot]
  have hbox : baseBox B = Set.pi s t ∩ stageSet 0 := by
    ext x
    change (∀ i, i ∈ Set.univ → x i ∈ B i) ↔
      ((∀ i, i ∈ (s : Set ℕ) → x i ∈ t i) ∧ ∀ i, 0 ≤ i → x i ∈ baseInterval)
    constructor
    · intro hx
      constructor
      · intro i hi
        have he := hx i (mem_univ _)
        have hi' : i ∈ s := hi
        have he' : x i ∈ t i ∩ baseInterval := by
          dsimp only [B] at he
          rw [if_pos hi'] at he
          exact he
        exact he'.1
      · intro i _
        have he := hx i (mem_univ _)
        by_cases hi : i ∈ s
        · have he' : x i ∈ t i ∩ baseInterval := by simpa only [B, if_pos hi] using he
          exact he'.2
        · simpa only [B, if_neg hi] using he
    · rintro ⟨hx, hi⟩ i _
      by_cases hs : i ∈ s
      · exact (by simpa only [B, if_pos hs] using And.intro (hx i hs) (hi i (Nat.zero_le _)))
      · simpa only [B, if_neg hs] using hi i (Nat.zero_le _)
  have hprod : (∏ i : Fin M, exponentialMeasure (B i)) = ∏ i ∈ s, baseMeasure (t i) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => exponentialMeasure (B i)) M]
    have hsub : (∏ i ∈ s, exponentialMeasure (B i)) =
        ∏ i ∈ Finset.range M, exponentialMeasure (B i) := by
      apply Finset.prod_subset hsM
      intro k _ hk
      rw [show B k = baseInterval from if_neg hk, exponentialMeasure_baseInterval]
    rw [← hsub]
    apply Finset.prod_congr rfl
    intro i hi
    rw [show B i = t i ∩ baseInterval from if_pos hi,
      baseMeasure, Measure.restrict_apply (ht i)]
  have he := shifted_restricted_box_mass h hh B hBm M hBtail
  rw [hbox, hprod] at he
  exact he

theorem shifted_restricted_restrict_base (h : RealSequences)
    (hh : Summable (fun n => |h n|)) :
    (restrictedProductMeasure.map (fun x => x + h)).restrict (stageSet 0) =
      ENNReal.ofReal (Real.exp (∑' n, h n)) • tailProbability := by
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (∑' n, h n))
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  let ν : Measure RealSequences :=
    (restrictedProductMeasure.map (fun x => x + h)).restrict (stageSet 0)
  let ξ : Measure RealSequences := c⁻¹ • ν
  have hξ : ξ = tailProbability := by
    change ξ = Measure.infinitePi (fun _ : ℕ => baseMeasure)
    apply Measure.eq_infinitePi
    intro s t ht
    change c⁻¹ * ν (Set.pi s t) = _
    rw [show ν (Set.pi s t) = c * ∏ i ∈ s, baseMeasure (t i) from by
      dsimp only [ν]
      rw [Measure.restrict_apply (MeasurableSet.pi (Finset.countable_toSet s) (fun i _ => ht i))]
      exact shifted_restricted_cylinder_mass h hh s t ht]
    rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  have he := congrArg (fun μ : Measure RealSequences => c • μ) hξ
  dsimp only [ξ] at he
  rw [smul_smul, ENNReal.mul_inv_cancel hc0 hct, one_smul] at he
  exact he

theorem map_translation_comm (μ : Measure RealSequences) (h k : RealSequences) :
    (μ.map (fun x => x + h)).map (fun x => x + k) =
      (μ.map (fun x => x + k)).map (fun x => x + h) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  exact add_right_comm x h k

theorem map_finiteShift_restrictedProductMeasure (n : ℕ) (q : Fin n → ℚ) :
    restrictedProductMeasure.map (fun x => x + finiteShift n q) =
      ENNReal.ofReal (Real.exp (∑ i : Fin n, (q i : ℝ))) • restrictedProductMeasure := by
  rw [map_finite_support_restrictedProductMeasure (finiteShift n q) n
    (fun k hk => finiteShift_tail n q k hk)]
  have he : (∑ k ∈ Finset.range n, finiteShift n q k) = ∑ i : Fin n, (q i : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => finiteShift n q k) n]
    exact finiteShift_sum n n le_rfl q
  rw [he]

/-- The translation-modulus assertion for every absolutely summable shift. -/
theorem map_summable_restrictedProductMeasure (h : RealSequences)
    (hh : Summable (fun n => |h n|)) :
    restrictedProductMeasure.map (fun x => x + h) =
      ENNReal.ofReal (Real.exp (∑' n, h n)) • restrictedProductMeasure := by
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (∑' n, h n))
  let μ : Measure RealSequences := restrictedProductMeasure.map (fun x => x + h)
  have hbase : μ.restrict (stageSet 0) = (c • restrictedProductMeasure).restrict (stageSet 0) := by
    rw [Measure.restrict_smul, restrictedProductMeasure_restrict 0, stageMeasure_zero]
    exact shifted_restricted_restrict_base h hh
  have hloc (n : ℕ) : μ.restrict (stageSet n) =
      (c • restrictedProductMeasure).restrict (stageSet n) := by
    rw [← iUnion_shiftedBase n]
    apply Measure.restrict_iUnion_congr.mpr
    intro q
    let d : RealSequences := finiteShift n q
    let k : ℝ≥0∞ := ENNReal.ofReal (Real.exp (∑ i : Fin n, (q i : ℝ)))
    have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hkt : k ≠ ∞ := ENNReal.ofReal_ne_top
    have hm : restrictedProductMeasure.map (fun x => x + d) = k • restrictedProductMeasure :=
      map_finiteShift_restrictedProductMeasure n q
    apply restrict_image_eq_of_same_modulus μ (c • restrictedProductMeasure)
      (shiftEquiv d) (stageSet 0) k hk0 hkt
    · change (restrictedProductMeasure.map (fun x => x + h)).map (fun x => x + d) = _
      rw [map_translation_comm, hm, Measure.map_smul]
    · change (c • restrictedProductMeasure).map (fun x => x + d) = _
      rw [Measure.map_smul, hm, smul_smul, smul_smul, mul_comm c k]
    · exact hbase
  have hX : μ.restrict restrictedProductSpace =
      (c • restrictedProductMeasure).restrict restrictedProductSpace :=
    Measure.restrict_iUnion_congr.mpr hloc
  have hμ : μ.restrict restrictedProductSpace = μ :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]
      exact map_shift_restrictedProductMeasure_compl h hh)
  have hσ : restrictedProductMeasure.restrict restrictedProductSpace = restrictedProductMeasure :=
    restrictedProductStages.limit_eq_restrict_union
  rw [hμ, Measure.restrict_smul, hσ] at hX
  exact hX

end MeasureEquivalenceRestrictedProduct



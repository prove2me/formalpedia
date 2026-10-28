-- Prove2me | solution 1 for MeasureEquivalenceRestrictedProduct.exists_zeroSum_shift_to_base
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:38:05.66834+00:00
-- url     : https://prove2.me/submissions/7cdb256f-6aab-4b16-92bb-f06085b23586

import Definitions.Def_BenchmarkOperator20261026_RestrictedAction
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedCorrection
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedSaturation
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finsupp.Encodable
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





theorem spreadFinsupp_mem (s : Finset ℕ) (r : ℚ) (k : ℕ) (hk : k ∈ s) :
    spreadFinsupp s r k = r := by
  classical
  simp [spreadFinsupp, Finsupp.finset_sum_apply, Finsupp.single_apply, hk]

theorem spreadFinsupp_notMem (s : Finset ℕ) (r : ℚ) (k : ℕ) (hk : k ∉ s) :
    spreadFinsupp s r k = 0 := by
  classical
  simp [spreadFinsupp, Finsupp.finset_sum_apply, Finsupp.single_apply, hk]

theorem rationalTotal_spreadFinsupp (s : Finset ℕ) (r : ℚ) :
    rationalTotal (spreadFinsupp s r) = (s.card : ℚ) * r := by
  simp [spreadFinsupp, map_sum, rationalTotal_single, nsmul_eq_mul]



end MeasureEquivalenceRestrictedProduct

end

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct

theorem solution (x : RealSequences)
    (hx : x ∈ restrictedProductSpace)
    (hfreq : ∃ᶠ k in atTop, x k ∈ innerInterval) :
    ∃ q : rationalZeroSumGroup, rationalTranslation q x ∈ stageSet 0 := by
  classical
  obtain ⟨N, hN⟩ := mem_iUnion.mp hx
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq (i : Fin N) : ∃ q : ℚ,
      -Real.log 2 - x i < (q : ℝ) ∧ (q : ℝ) < -x i :=
    exists_rat_btwn (by linarith)
  choose q hqlo hqhi using hq
  let a : ℕ →₀ ℚ := headFinsupp N q
  let s : ℚ := rationalTotal a
  let δ : ℝ := Real.log 2 / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (|(s : ℝ)| / δ)
  have hMpos : 0 < (M : ℝ) := lt_of_le_of_lt (div_nonneg (abs_nonneg _) hδ.le) hM
  have hMnat : 0 < M := by exact_mod_cast hMpos
  have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hMnat)
  let r : ℚ := -s / M
  have hr : |(r : ℝ)| < δ := by
    have he : |(r : ℝ)| = |(s : ℝ)| / M := by
      dsimp only [r]
      push_cast
      rw [abs_div, abs_neg, abs_of_pos hMpos]
    rw [he]
    apply (div_lt_iff₀ hMpos).mpr
    have he' := (div_lt_iff₀ hδ).mp hM
    linarith
  have hInf : {k : ℕ | N ≤ k ∧ x k ∈ innerInterval}.Infinite := by
    rw [← Nat.frequently_atTop_iff_infinite]
    exact (hfreq.and_eventually (eventually_ge_atTop N)).mono (fun k hk => ⟨hk.2, hk.1⟩)
  obtain ⟨S, hS, hScard⟩ := hInf.exists_subset_card_eq M
  let d : ℕ →₀ ℚ := a + spreadFinsupp S r
  have hd : rationalTotal d = 0 := by
    dsimp only [d]
    rw [map_add, rationalTotal_spreadFinsupp, hScard]
    change s + (M : ℚ) * (-s / M) = 0
    field_simp
    ring
  refine ⟨⟨d, hd⟩, ?_⟩
  intro k _
  change x k + (d k : ℝ) ∈ baseInterval
  by_cases hk : k < N
  · have hnot : k ∉ S := by
      intro hkS
      have := (hS hkS).1
      omega
    have hda : d k = q ⟨k, hk⟩ := by
      dsimp only [d, a]
      rw [Finsupp.add_apply, headFinsupp_head N q ⟨k, hk⟩,
        spreadFinsupp_notMem S r k hnot, add_zero]
    rw [hda]
    constructor <;> linarith [hqlo ⟨k, hk⟩, hqhi ⟨k, hk⟩]
  · have hnk : N ≤ k := le_of_not_gt hk
    by_cases hkS : k ∈ S
    · have hda : d k = r := by
        dsimp only [d, a]
        rw [Finsupp.add_apply, headFinsupp_tail N q k hnk,
          spreadFinsupp_mem S r k hkS, zero_add]
      rw [hda]
      have hJ := (hS hkS).2
      have hr' := abs_lt.mp hr
      constructor <;> dsimp [innerInterval] at hJ <;> dsimp [δ] at hr' <;>
        linarith [hJ.1, hJ.2, hr'.1, hr'.2]
    · have hda : d k = 0 := by
        dsimp only [d, a]
        rw [Finsupp.add_apply, headFinsupp_tail N q k hnk,
          spreadFinsupp_notMem S r k hkS, add_zero]
      rw [hda, Rat.cast_zero, add_zero]
      exact hN k hnk

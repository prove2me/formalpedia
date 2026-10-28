-- Prove2me | solution 1 for MeasureEquivalenceHellinger.tendsto_integral_regularized_root_tests
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:29:41.020795+00:00
-- url     : https://prove2.me/submissions/f88648dd-eccb-4f0a-be1e-cf95bc8024c2

import Definitions.Def_BenchmarkOperator20261026_HellingerVariational
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
import Mathlib.Topology.Semicontinuity.Basic

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

-- Preserved source skeleton: HellingerVariational
section
/-! Continuous positive test functions for Hellinger affinity. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceHellinger













private theorem regularizer_pos (n : ℕ) : 0 < regularizer n := by
  unfold regularizer
  positivity

private theorem regularizer_le_one (n : ℕ) : regularizer n ≤ 1 := by
  unfold regularizer
  apply (div_le_one (by positivity)).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem regularizer_tendsto : Tendsto regularizer atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem weighted_ratio_le_two (p q d : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hd : 0 < d) (hd1 : d ≤ 1) :
    p * ((Real.sqrt q + d) / (Real.sqrt p + d)) ≤ 2 := by
  have hden : 0 < Real.sqrt p + d := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hd
  have hpdiv : p / (Real.sqrt p + d) ≤ Real.sqrt p := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p]
  have hsp : Real.sqrt p ≤ 1 := by nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p]
  have hsq : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q]
  calc
    _ = (p / (Real.sqrt p + d)) * (Real.sqrt q + d) := by ring
    _ ≤ Real.sqrt p * (Real.sqrt q + d) :=
      mul_le_mul_of_nonneg_right hpdiv (by positivity)
    _ ≤ 1 * 2 := mul_le_mul hsp (by linarith) (by positivity) (by norm_num)
    _ = 2 := by ring

private theorem weighted_ratio_tendsto (p q : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun n => p * ((Real.sqrt q + regularizer n) /
      (Real.sqrt p + regularizer n))) atTop (𝓝 (Real.sqrt p * Real.sqrt q)) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hsp : Real.sqrt p ≠ 0 :=
    (Real.sqrt_pos.mpr (lt_of_le_of_ne hp (fun h => hp0 h.symm))).ne'
  have ht : Tendsto (fun n => p * ((Real.sqrt q + regularizer n) /
      (Real.sqrt p + regularizer n))) atTop
      (𝓝 (p * ((Real.sqrt q + 0) / (Real.sqrt p + 0)))) :=
    tendsto_const_nhds.mul
      ((tendsto_const_nhds.add regularizer_tendsto).div
        (tendsto_const_nhds.add regularizer_tendsto) (by simpa using hsp))
  have hlim : p * ((Real.sqrt q + 0) / (Real.sqrt p + 0)) =
      Real.sqrt p * Real.sqrt q := by
    simp only [add_zero]
    nth_rw 1 [← Real.sq_sqrt hp]
    field_simp
  rw [hlim] at ht
  exact ht



section Compact

variable {Z : Type*} [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]



























end Compact

end MeasureEquivalenceHellinger

end

/-! Continuous positive test functions for Hellinger affinity. -/
open MeasureTheory Filter
open scoped ENNReal Topology
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
open MeasureEquivalenceHellinger

theorem solution
    {Z : Type*} [MeasurableSpace Z] (ρ : Measure Z) [IsFiniteMeasure ρ]
    (P Q : Z → ℝ) (hP : Measurable P) (hQ : Measurable Q)
    (hPbound : ∀ z, 0 ≤ P z ∧ P z ≤ 1)
    (hQbound : ∀ z, 0 ≤ Q z ∧ Q z ≤ 1) :
    Tendsto (fun n => ∫ z,
      (P z * ((Real.sqrt (Q z) + regularizer n) / (Real.sqrt (P z) + regularizer n)) +
       Q z * ((Real.sqrt (Q z) + regularizer n) / (Real.sqrt (P z) + regularizer n))⁻¹) / 2 ∂ρ)
      atTop (𝓝 (∫ z, Real.sqrt (P z) * Real.sqrt (Q z) ∂ρ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
  · intro n
    exact ((hP.mul ((hQ.sqrt.add_const _).div (hP.sqrt.add_const _))).add
      (hQ.mul ((hQ.sqrt.add_const _).div (hP.sqrt.add_const _)).inv)).div_const 2
      |>.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    apply Eventually.of_forall
    intro z
    have hp0 := (hPbound z).1
    have hq0 := (hQbound z).1
    have hd0 := regularizer_pos n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [inv_div]
    have h1 := weighted_ratio_le_two (P z) (Q z) (regularizer n)
      (hPbound z).1 (hPbound z).2 (hQbound z).1 (hQbound z).2
      (regularizer_pos n) (regularizer_le_one n)
    have h2 := weighted_ratio_le_two (Q z) (P z) (regularizer n)
      (hQbound z).1 (hQbound z).2 (hPbound z).1 (hPbound z).2
      (regularizer_pos n) (regularizer_le_one n)
    linarith
  · apply Eventually.of_forall
    intro z
    have h1 := weighted_ratio_tendsto (P z) (Q z) (hPbound z).1
    have h2 := weighted_ratio_tendsto (Q z) (P z) (hQbound z).1
    have ht := (h1.add h2).div_const 2
    convert ht using 1
    · ext n
      rw [inv_div]
    · congr 1
      ring

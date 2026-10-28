-- Prove2me | solution 1 for MeasureEquivalenceHellinger.exists_measurable_affinityTest_lt
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:30:28.922977+00:00
-- url     : https://prove2.me/submissions/1bd72b4c-f322-4bc4-8848-4b5f886c17d4

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_HellingerVariational
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_MeasureEquivalenceHellinger_tendsto_integral_regularized_root_tests

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











section Compact

variable {Z : Type*} [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]



omit [MetricSpace Z] [CompactSpace Z] [BorelSpace Z] in
private theorem integrable_of_Icc (ρ : Measure Z) [IsFiniteMeasure ρ]
    (f : Z → ℝ) (hf : Measurable f) (c C : ℝ) (hc : 0 < c)
    (hfbound : ∀ z, c ≤ f z ∧ f z ≤ C) : Integrable f ρ := by
  apply Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
  exact Eventually.of_forall (fun z => by
    simpa [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hfbound z).1)] using (hfbound z).2)

omit [MetricSpace Z] [CompactSpace Z] [BorelSpace Z] in
private theorem inverse_integrable_of_Ici (ρ : Measure Z) [IsFiniteMeasure ρ]
    (f : Z → ℝ) (hf : Measurable f) (c : ℝ) (hc : 0 < c)
    (hfbound : ∀ z, c ≤ f z) : Integrable (fun z => (f z)⁻¹) ρ := by
  apply Integrable.mono' (integrable_const c⁻¹) hf.inv.aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hc.trans_le (hfbound z)))]
  exact inv_le_inv₀ (hc.trans_le (hfbound z)) hc |>.mpr (hfbound z)



private theorem ratio_bounds (p q d : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hd : 0 < d) :
    d / (1 + d) ≤ (Real.sqrt q + d) / (Real.sqrt p + d) ∧
      (Real.sqrt q + d) / (Real.sqrt p + d) ≤ (1 + d) / d := by
  have hsp : Real.sqrt p ≤ 1 := by nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p]
  have hsq : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q]
  have hden : 0 < Real.sqrt p + d := by positivity
  constructor
  · calc
      d / (1 + d) ≤ (Real.sqrt q + d) / (1 + d) :=
        div_le_div_of_nonneg_right (by linarith [Real.sqrt_nonneg q]) (by positivity)
      _ ≤ (Real.sqrt q + d) / (Real.sqrt p + d) :=
        div_le_div_of_nonneg_left (by positivity) hden (by linarith)
  · calc
      _ ≤ (1 + d) / (Real.sqrt p + d) := by gcongr
      _ ≤ (1 + d) / d := div_le_div_of_nonneg_left (by positivity) hd
        (by linarith [Real.sqrt_nonneg p])

















end Compact

end MeasureEquivalenceHellinger

end

/-! Continuous positive test functions for Hellinger affinity. -/
open MeasureTheory Filter
open scoped ENNReal Topology
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
open MeasureEquivalenceHellinger
variable {Z : Type*} [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]

omit [MetricSpace Z] [CompactSpace Z] [BorelSpace Z]

theorem solution
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : ℝ) (hη : 0 < η) :
    ∃ (f : Z → ℝ) (c C : ℝ), Measurable f ∧ 0 < c ∧ c ≤ C ∧
      (∀ z, c ≤ f z ∧ f z ≤ C) ∧ affinityTest μ ν f < affinity μ ν + η := by
  let P : Z → ℝ := fun z => min (μ.rnDeriv (μ + ν) z).toReal 1
  let Q : Z → ℝ := fun z => min (ν.rnDeriv (μ + ν) z).toReal 1
  have hPm : Measurable P := (Measure.measurable_rnDeriv _ _).ennreal_toReal.min measurable_const
  have hQm : Measurable Q := (Measure.measurable_rnDeriv _ _).ennreal_toReal.min measurable_const
  have hPb : ∀ z, 0 ≤ P z ∧ P z ≤ 1 := fun z =>
    ⟨le_min ENNReal.toReal_nonneg zero_le_one, min_le_right _ _⟩
  have hQb : ∀ z, 0 ≤ Q z ∧ Q z ≤ 1 := fun z =>
    ⟨le_min ENNReal.toReal_nonneg zero_le_one, min_le_right _ _⟩
  have hμle : μ ≤ μ + ν := Measure.le_add_right le_rfl
  have hνle : ν ≤ μ + ν := Measure.le_add_left le_rfl
  have hμ : μ ≪ μ + ν := hμle.absolutelyContinuous
  have hν : ν ≪ μ + ν := hνle.absolutelyContinuous
  have hPeq : P =ᵐ[μ + ν] fun z => (μ.rnDeriv (μ + ν) z).toReal := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hμle] with z hz
    exact min_eq_left (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hz)
  have hQeq : Q =ᵐ[μ + ν] fun z => (ν.rnDeriv (μ + ν) z).toReal := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hνle] with z hz
    exact min_eq_left (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hz)
  let F : ℕ → Z → ℝ := fun n z =>
    (Real.sqrt (Q z) + regularizer n) / (Real.sqrt (P z) + regularizer n)
  have hFm : ∀ n, Measurable (F n) := fun n =>
    (hQm.sqrt.add_const _).div (hPm.sqrt.add_const _)
  have hFb : ∀ n z,
      regularizer n / (1 + regularizer n) ≤ F n z ∧
        F n z ≤ (1 + regularizer n) / regularizer n := by
    intro n z
    exact ratio_bounds (P z) (Q z) (regularizer n)
      (hPb z).1 (hPb z).2 (hQb z).1 (hQb z).2 (regularizer_pos n)
  have hcpos : ∀ n, 0 < regularizer n / (1 + regularizer n) := fun n => by
    have hd := regularizer_pos n
    positivity
  have hcC : ∀ n, regularizer n / (1 + regularizer n) ≤
      (1 + regularizer n) / regularizer n := by
    intro n
    calc
      _ ≤ 1 := (div_le_one (by have hd := regularizer_pos n; positivity)).mpr (by linarith)
      _ ≤ _ := (one_le_div (regularizer_pos n)).mpr (by linarith)
  have hcost : ∀ n,
      (∫ z, (P z * F n z + Q z * (F n z)⁻¹) / 2 ∂(μ + ν)) =
        affinityTest μ ν (F n) := by
    intro n
    have hfμ := integrable_of_Icc μ (F n) (hFm n) _ _ (hcpos n) (hFb n)
    have hfinvν := inverse_integrable_of_Ici ν (F n) (hFm n) _ (hcpos n)
      (fun z => (hFb n z).1)
    have hiP := (integrable_toReal_rnDeriv_mul_iff hμ).mpr hfμ
    have hiQ := (integrable_toReal_rnDeriv_mul_iff hν).mpr hfinvν
    have hcongr :
        (fun z => (P z * F n z + Q z * (F n z)⁻¹) / 2) =ᵐ[μ + ν]
        (fun z => ((μ.rnDeriv (μ + ν) z).toReal * F n z +
          (ν.rnDeriv (μ + ν) z).toReal * (F n z)⁻¹) / 2) := by
      filter_upwards [hPeq, hQeq] with z hp hq
      rw [hp, hq]
    rw [integral_congr_ae hcongr, integral_div, integral_add hiP hiQ,
      integral_toReal_rnDeriv_mul hμ, integral_toReal_rnDeriv_mul hν]
    rfl
  have hlimitEq : (∫ z, Real.sqrt (P z) * Real.sqrt (Q z) ∂(μ + ν)) = affinity μ ν := by
    rw [affinity_integral]
    apply integral_congr_ae
    filter_upwards [hPeq, hQeq] with z hp hq
    rw [hp, hq]
  have ht := tendsto_integral_regularized_root_tests (μ + ν) P Q hPm hQm hPb hQb
  change Tendsto (fun n => ∫ z, (P z * F n z + Q z * (F n z)⁻¹) / 2 ∂(μ + ν))
    atTop (𝓝 _) at ht
  simp_rw [hcost, hlimitEq] at ht
  obtain ⟨n, hn⟩ := ((tendsto_order.1 ht).2 (affinity μ ν + η) (by linarith)).exists
  exact ⟨F n, _, _, hFm n, hcpos n, hcC n, hFb n, hn⟩

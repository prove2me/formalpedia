-- Prove2me | solution 1 for MeasureEquivalenceHellinger.exists_continuous_affinityTest_le
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:30:14.72314+00:00
-- url     : https://prove2.me/submissions/842f9d05-698e-421b-9679-2f1c91ef2efc

import Definitions.Def_BenchmarkOperator20261026_HellingerVariational
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_MeasureEquivalenceHellinger_exists_continuous_Icc_integral_sub_le

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





private theorem inverse_lipschitz_on_Ici (c u v : ℝ) (hc : 0 < c)
    (hu : c ≤ u) (hv : c ≤ v) :
    |u⁻¹ - v⁻¹| ≤ (c * c)⁻¹ * |u - v| := by
  have hu0 : 0 < u := hc.trans_le hu
  have hv0 : 0 < v := hc.trans_le hv
  rw [inv_sub_inv hu0.ne' hv0.ne', abs_div,
    abs_of_pos (mul_pos hu0 hv0), abs_sub_comm v u]
  have huv : c * c ≤ u * v := mul_le_mul hu hv hc.le hu0.le
  calc
    |u - v| / (u * v) ≤ |u - v| / (c * c) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hc hc) huv
    _ = _ := by ring



















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

theorem solution
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : Z → ℝ) (hf : Measurable f)
    (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C)
    (hfbound : ∀ z, c ≤ f z ∧ f z ≤ C)
    (η : ℝ) (hη : 0 < η) :
    ∃ g : C(Z, ℝ), (∀ z, 0 < g z) ∧
      affinityTest μ ν g ≤ affinityTest μ ν f + η := by
  let L : ℝ := (c * c)⁻¹
  have hL : 0 ≤ L := le_of_lt (inv_pos.mpr (mul_pos hc hc))
  let δ : ℝ := η / (1 + L)
  have hδ : 0 < δ := div_pos hη (by positivity)
  obtain ⟨g, hgbound, hgδ⟩ := exists_continuous_Icc_integral_sub_le (μ + ν) f
    (integrable_of_Icc (μ + ν) f hf c C hc hfbound) c C hcC hfbound δ hδ
  refine ⟨g, (fun z => hc.trans_le (hgbound z).1), ?_⟩
  have hμle : μ ≤ μ + ν := Measure.le_add_right le_rfl
  have hνle : ν ≤ μ + ν := Measure.le_add_left le_rfl
  have hfi : Integrable f (μ + ν) := integrable_of_Icc _ f hf c C hc hfbound
  have hgi : Integrable g (μ + ν) := (BoundedContinuousFunction.mkOfCompact g).integrable _
  have hdiff : Integrable (fun z => ‖f z - g z‖) (μ + ν) := (hfi.sub hgi).norm
  have hδμ : (∫ z, ‖f z - g z‖ ∂μ) ≤ δ :=
    (integral_mono_measure hμle (Eventually.of_forall (fun z => norm_nonneg _)) hdiff).trans hgδ
  have hδν : (∫ z, ‖f z - g z‖ ∂ν) ≤ δ :=
    (integral_mono_measure hνle (Eventually.of_forall (fun z => norm_nonneg _)) hdiff).trans hgδ
  have hfμ := hfi.mono_measure hμle
  have hgμ := hgi.mono_measure hμle
  have hfνinv := inverse_integrable_of_Ici ν f hf c hc (fun z => (hfbound z).1)
  have hgνinv := inverse_integrable_of_Ici ν g g.continuous.measurable c hc
    (fun z => (hgbound z).1)
  have hμcost : (∫ z, g z ∂μ) ≤ (∫ z, f z ∂μ) + δ := by
    have hnorm := norm_integral_le_integral_norm (fun z => g z - f z) (μ := μ)
    rw [integral_sub hgμ hfμ, Real.norm_eq_abs] at hnorm
    have hnorm' : (∫ z, ‖g z - f z‖ ∂μ) = ∫ z, ‖f z - g z‖ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => norm_sub_rev _ _)
    rw [hnorm'] at hnorm
    have hle := le_abs_self ((∫ z, g z ∂μ) - ∫ z, f z ∂μ)
    linarith
  have hνcost : (∫ z, (g z)⁻¹ ∂ν) ≤ (∫ z, (f z)⁻¹ ∂ν) + L * δ := by
    have hnorm := norm_integral_le_integral_norm (fun z => (g z)⁻¹ - (f z)⁻¹) (μ := ν)
    rw [integral_sub hgνinv hfνinv, Real.norm_eq_abs] at hnorm
    have hbound : (∫ z, ‖(g z)⁻¹ - (f z)⁻¹‖ ∂ν) ≤
        L * ∫ z, ‖f z - g z‖ ∂ν := by
      rw [← integral_const_mul]
      apply integral_mono (hgνinv.sub hfνinv).norm ((hdiff.mono_measure hνle).const_mul L)
      intro z
      simpa only [Real.norm_eq_abs, abs_sub_comm (g z)] using
        inverse_lipschitz_on_Ici c (g z) (f z) hc (hgbound z).1 (hfbound z).1
    have hmul := mul_le_mul_of_nonneg_left hδν hL
    have hle := le_abs_self ((∫ z, (g z)⁻¹ ∂ν) - ∫ z, (f z)⁻¹ ∂ν)
    linarith
  have hcancel : δ + L * δ = η := by
    dsimp [δ]
    field_simp
  unfold affinityTest
  linarith

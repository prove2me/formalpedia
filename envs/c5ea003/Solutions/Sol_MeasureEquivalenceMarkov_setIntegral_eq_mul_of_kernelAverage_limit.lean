-- Prove2me | solution 1 for MeasureEquivalenceMarkov.setIntegral_eq_mul_of_kernelAverage_limit
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:26:57.169266+00:00
-- url     : https://prove2.me/submissions/7571437c-4f02-4098-9ecf-1473519a33fc

import Definitions.Def_BenchmarkOperator20261026_KernelAverages
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Definitions.Def_BenchmarkOperator20261026_OrbitMarkov
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Tactic

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

-- Preserved source skeleton: KernelAverages
section
/-! Actual bounded kernel iterates, Cesaro averages, and almost-everywhere
subsequences of their Hilbert mean-ergodic limits. -/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal Topology

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]







theorem kernelApply_measurable (P : Kernel Z Z) (f : Z → ℝ) (hf : Measurable f) :
    Measurable (kernelApply P f) := hf.stronglyMeasurable.integral_kernel.measurable

theorem kernelIterate_measurable (P : Kernel Z Z) (f : Z → ℝ) (hf : Measurable f) :
    ∀ n, Measurable (kernelIterate P f n) := by
  intro n
  induction n with
  | zero => exact hf
  | succ n ih => exact kernelApply_measurable P _ ih

theorem kernelAverage_measurable (P : Kernel Z Z) (f : Z → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (kernelAverage P f n) :=
  measurable_const.mul (Finset.measurable_sum _ (fun k _ => kernelIterate_measurable P f hf k))

theorem kernelApply_abs_le (P : Kernel Z Z) [IsMarkovKernel P]
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (_hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C) :
    ∀ z, |kernelApply P f z| ≤ C := by
  intro z
  have hfi : Integrable f (P z) := Integrable.mono' (integrable_const C)
    hf.aestronglyMeasurable (Eventually.of_forall (fun y => by simpa using hfC y))
  calc
    _ ≤ ∫ y, ‖f y‖ ∂P z := norm_integral_le_integral_norm f
    _ ≤ ∫ _ : Z, C ∂P z := integral_mono hfi.norm (integrable_const C) (fun y => by simpa using hfC y)
    _ = C := by simp

theorem kernelIterate_abs_le (P : Kernel Z Z) [IsMarkovKernel P]
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C) :
    ∀ n z, |kernelIterate P f n z| ≤ C := by
  intro n
  induction n with
  | zero => exact hfC
  | succ n ih => exact kernelApply_abs_le P _ (kernelIterate_measurable P f hf n) C hC ih

theorem kernelAverage_abs_le (P : Kernel Z Z) [IsMarkovKernel P]
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C) :
    ∀ n z, |kernelAverage P f n z| ≤ C := by
  intro n z
  by_cases hn : n = 0
  · simpa [kernelAverage, hn] using hC
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsum : |∑ k ∈ range n, kernelIterate P f k z| ≤ (n : ℝ) * C := by
    calc
      _ ≤ ∑ k ∈ range n, |kernelIterate P f k z| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ range n, C := sum_le_sum (fun k _ => kernelIterate_abs_le P f hf C hC hfC k z)
      _ = (n : ℝ) * C := by simp
  rw [kernelAverage, abs_mul, abs_of_pos (inv_pos.mpr hnpos)]
  calc
    _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * C) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C := by field_simp



theorem kernelApply_integral_of_stationary (ν : Measure Z) [SFinite ν] (P : Kernel Z Z)
    [IsSFiniteKernel P] (hstationary : P ∘ₘ ν = ν)
    (f : Z → ℝ) (hf : Integrable f ν) :
    (∫ z, kernelApply P f z ∂ν) = ∫ z, f z ∂ν := by
  have hfi : Integrable f ((P ∘ₖ Kernel.const Unit ν) ()) := by
    rw [← Measure.comp_eq_comp_const_apply, hstationary]
    exact hf
  have h := ProbabilityTheory.Kernel.integral_comp hfi
  simpa only [← Measure.comp_eq_comp_const_apply, hstationary, Kernel.const_apply] using h.symm

theorem kernelIterate_setIntegral (ν : Measure Z) [IsFiniteMeasure ν]
    (P : Kernel Z Z) [IsMarkovKernel P]
    (s : Set Z) (hstationary : P ∘ₘ (ν.restrict s) = ν.restrict s)
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C) :
    ∀ n, (∫ z in s, kernelIterate P f n z ∂ν) = ∫ z in s, f z ∂ν := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∫ z in s, kernelApply P (kernelIterate P f n) z ∂ν) = _
    rw [kernelApply_integral_of_stationary (ν.restrict s) P hstationary]
    · exact ih
    · apply Integrable.mono' (integrable_const C)
        (kernelIterate_measurable P f hf n).aestronglyMeasurable
      exact Eventually.of_forall (fun z => by
        simpa using kernelIterate_abs_le P f hf C hC hfC n z)

theorem kernelAverage_setIntegral (ν : Measure Z) [IsFiniteMeasure ν]
    (P : Kernel Z Z) [IsMarkovKernel P]
    (s : Set Z) (hstationary : P ∘ₘ (ν.restrict s) = ν.restrict s)
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C)
    (n : ℕ) (hn : n ≠ 0) :
    (∫ z in s, kernelAverage P f n z ∂ν) = ∫ z in s, f z ∂ν := by
  have hI (k : ℕ) : Integrable (kernelIterate P f k) (ν.restrict s) := by
    apply Integrable.mono' (integrable_const C) (kernelIterate_measurable P f hf k).aestronglyMeasurable
    exact Eventually.of_forall (fun z => by simpa using kernelIterate_abs_le P f hf C hC hfC k z)
  unfold kernelAverage
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hI k)]
  simp_rw [kernelIterate_setIntegral ν P s hstationary f hf C hC hfC]
  simp only [sum_const, card_range, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp





section L2

variable (μ : Measure Z) (P : Kernel Z Z)
    (hstationary : P ∘ₘ μ = μ)
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hL : ∀ f : Lp ℝ 2 μ, L f =ᵐ[μ] kernelApply P f)

include hstationary hL







end L2

end MeasureEquivalenceMarkov

end

/-! Actual bounded kernel iterates, Cesaro averages, and almost-everywhere
subsequences of their Hilbert mean-ergodic limits. -/
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal Topology
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
open MeasureEquivalenceMarkov
variable {Z : Type*} [MeasurableSpace Z]

theorem solution
    (ν : Measure Z) [IsFiniteMeasure ν] (P : Kernel Z Z) [IsMarkovKernel P]
    (s : Set Z) (hstationary : P ∘ₘ (ν.restrict s) = ν.restrict s)
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C)
    (ns : ℕ → ℕ) (hns : StrictMono ns) (c : ℝ)
    (hlimit : ∀ᵐ z ∂ν, Tendsto (fun n => kernelAverage P f (ns n) z) atTop (𝓝 c)) :
    (∫ z in s, f z ∂ν) = c * ν.real s := by
  have ht : Tendsto (fun n => ∫ z in s, kernelAverage P f (ns n) z ∂ν)
      atTop (𝓝 (∫ _z in s, c ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · intro n
      exact (kernelAverage_measurable P f hf (ns n)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall (fun z => by simpa using kernelAverage_abs_le P f hf C hC hfC (ns n) z)
    · exact ae_restrict_of_ae hlimit
  have hconst : (fun n => ∫ z in s, kernelAverage P f (ns n) z ∂ν) =ᶠ[atTop]
      fun _ => ∫ z in s, f z ∂ν := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : ns n ≠ 0 := by
      intro hz
      have hid : n ≤ ns n := hns.id_le n
      rw [hz] at hid
      omega
    exact kernelAverage_setIntegral ν P s hstationary f hf C hC hfC (ns n) hn0
  have hconstlim : Tendsto (fun n => ∫ z in s, kernelAverage P f (ns n) z ∂ν)
      atTop (𝓝 (∫ z in s, f z ∂ν)) := tendsto_const_nhds.congr' hconst.symm
  have heq := tendsto_nhds_unique ht hconstlim
  rw [setIntegral_const, smul_eq_mul, mul_comm] at heq
  exact heq.symm

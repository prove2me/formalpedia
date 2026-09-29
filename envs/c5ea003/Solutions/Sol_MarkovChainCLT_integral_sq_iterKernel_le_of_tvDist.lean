-- Prove2me | solution 1 for MarkovChainCLT.integral_sq_iterKernel_le_of_tvDist
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T00:02:46.816821+00:00
-- url     : https://prove2.me/submissions/600b6b3f-0cd1-4640-802e-6caeec79a8d6

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_sqrt_tvDist_mul
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 1000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (N : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (h : X → ℝ) (hh : Measurable h) (hL2 : Integrable (fun x => (h x) ^ 2) π)
    (hmean : ∫ x, h x ∂π = 0) :
    ∫ x, (∫ y, h y ∂(iterKernel P N x)) ^ 2 ∂π ≤ 4 * ρ * ∫ x, (h x) ^ 2 ∂π := by
  classical
  -- `π` is invariant for every power of `P`
  have hinvN : ∀ n : ℕ, (iterKernel P n) ∘ₘ π = π := by
    intro n
    induction n with
    | zero =>
        rw [iterKernel_zero]
        simp
    | succ k ih =>
        rw [iterKernel_succ, ← Measure.comp_assoc, ih, hinv]
  -- Fubini for the composed measure
  have hcomp : (iterKernel P N) ∘ₘ π = ((iterKernel P N) ∘ₖ Kernel.const Unit π) () :=
    Measure.comp_eq_comp_const_apply
  have hsq_int : Integrable (fun y => (h y) ^ 2)
      (((iterKernel P N) ∘ₖ Kernel.const Unit π) ()) := by
    rw [← hcomp, hinvN N]
    exact hL2
  have hsq_intm : Integrable (fun y => (h y) ^ 2) ((iterKernel P N) ∘ₘ π) := by
    rw [hinvN N]; exact hL2
  set S : ℝ := ∫ x, (h x) ^ 2 ∂π with hS
  have hS0 : 0 ≤ S := integral_nonneg (fun x => sq_nonneg _)
  set A : X → ℝ := fun x => ∫ y, (h y) ^ 2 ∂(iterKernel P N x) with hA
  have hAm : Measurable A :=
    ((hh.pow_const 2).stronglyMeasurable.integral_kernel (κ := iterKernel P N)).measurable
  have hAint : Integrable A π := by
    have := Measure.integrable_integral_norm_of_integrable_comp
      (κ := iterKernel P N) (μ := π) (f := fun y => (h y) ^ 2) hsq_intm
    refine this.congr ?_
    filter_upwards with x
    refine integral_congr_ae (ae_of_all _ (fun y => ?_))
    simp only
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (h y))]
  have hAeq : ∫ x, A x ∂π = S := by
    have h1 : ∫ y, (h y) ^ 2 ∂((iterKernel P N) ∘ₘ π) = ∫ x, A x ∂π := by
      rw [hcomp, Kernel.integral_comp hsq_int]
      simp [hA]
    rw [← h1, hinvN N, hS]
  -- integrability of `h²` against the kernel, for `π`-almost every starting point
  have hae : ∀ᵐ x ∂π, Integrable (fun y => (h y) ^ 2) ((iterKernel P N) x) :=
    Measure.ae_integrable_of_integrable_comp hsq_intm
  -- the pointwise bound
  have hpt : ∀ᵐ x ∂π, (∫ y, h y ∂(iterKernel P N x)) ^ 2 ≤ 2 * ρ * (A x + S) := by
    filter_upwards [hae] with x hx
    have hcs := abs_integral_sub_le_sqrt_tvDist_mul (iterKernel P N x) π h hh hx hL2
    rw [hmean, sub_zero] at hcs
    have hA0 : 0 ≤ A x := integral_nonneg (fun y => sq_nonneg _)
    have hcs2 : |∫ y, h y ∂(iterKernel P N x)|
        ≤ Real.sqrt ρ * (Real.sqrt (A x) + Real.sqrt S) := by
      refine le_trans hcs ?_
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hρ x)) (by positivity)
    have hM0 : 0 ≤ Real.sqrt ρ * (Real.sqrt (A x) + Real.sqrt S) := by positivity
    have hsq : (∫ y, h y ∂(iterKernel P N x)) ^ 2
        ≤ ρ * (Real.sqrt (A x) + Real.sqrt S) ^ 2 := by
      have e : (Real.sqrt ρ * (Real.sqrt (A x) + Real.sqrt S)) ^ 2
          = ρ * (Real.sqrt (A x) + Real.sqrt S) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hρ0]
      rw [← e]
      nlinarith [hcs2, abs_nonneg (∫ y, h y ∂(iterKernel P N x)),
        sq_abs (∫ y, h y ∂(iterKernel P N x)), hM0]
    have hab : (Real.sqrt (A x) + Real.sqrt S) ^ 2 ≤ 2 * (A x + S) := by
      have e1 : Real.sqrt (A x) ^ 2 = A x := Real.sq_sqrt hA0
      have e2 : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0
      nlinarith [sq_nonneg (Real.sqrt (A x) - Real.sqrt S), e1, e2]
    nlinarith [hsq, mul_le_mul_of_nonneg_left hab hρ0]
  -- integrate
  have hlhsint : Integrable (fun x => (∫ y, h y ∂(iterKernel P N x)) ^ 2) π := by
    refine Integrable.mono' (g := fun x => 2 * ρ * (A x + S))
      (((hAint.add (integrable_const S)).const_mul (2 * ρ))) ?_ ?_
    · exact ((hh.stronglyMeasurable.integral_kernel
        (κ := iterKernel P N)).measurable.pow_const 2).aestronglyMeasurable
    · filter_upwards [hpt] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hx
  have hfin := integral_mono_ae hlhsint
    ((hAint.add (integrable_const S)).const_mul (2 * ρ)) hpt
  simp only [Pi.add_apply] at hfin
  rw [integral_const_mul, integral_add hAint (integrable_const S), integral_const, hAeq] at hfin
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hfin
  calc ∫ x, (∫ y, h y ∂(iterKernel P N x)) ^ 2 ∂π ≤ 2 * ρ * (S + S) := hfin
    _ = 4 * ρ * S := by ring

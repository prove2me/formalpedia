-- Prove2me | solution 1 for MarkovChainCLT.poissonEquation_of_bounded_of_uniformlyErgodic
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T23:01:07.715916+00:00
-- url     : https://prove2.me/submissions/c46a8b7a-19e1-4a1c-8fbb-fe1d3db47232

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist_of_bounded
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory Filter
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 1000000

theorem solution {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (huni : UniformlyErgodic P π)
    (φ : X → ℝ) (hφ : Measurable φ) (B : ℝ) (hB : ∀ x, |φ x| ≤ B) :
    ∃ g : X → ℝ, Measurable g ∧ (∃ C : ℝ, ∀ x, |g x| ≤ C) ∧
      ∀ x, g x - ∫ y, g y ∂(P x) = φ x - ∫ y, φ y ∂π := by
  classical
  obtain ⟨R, t, hR0, ht0, ht1, hrate⟩ := huni
  have hne : Nonempty X := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h1 : π Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr hcon, measure_empty] at h1
    exact zero_ne_one h1
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB hne.some)
  have habsφ : Measurable (fun x => |φ x|) := continuous_abs.measurable.comp hφ
  have hIntφ : ∀ (μ : Measure X), IsProbabilityMeasure μ → Integrable φ μ := by
    intro μ hμ
    exact ⟨hφ.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := B) (ae_of_all _ (fun z => by simpa using hB z))⟩
  have hIntBound : ∀ (μ : Measure X), IsProbabilityMeasure μ → |∫ z, φ z ∂μ| ≤ B := by
    intro μ hμ
    refine le_trans abs_integral_le_integral_abs ?_
    have h1 : Integrable (fun z => |φ z|) μ :=
      ⟨habsφ.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := B) (ae_of_all _ (fun z => by simpa using hB z))⟩
    have h2 := integral_mono h1 (integrable_const B) (fun z => hB z)
    simpa using h2
  set c₀ : ℝ := ∫ y, φ y ∂π with hc₀
  have hc₀B : |c₀| ≤ B := hIntBound π inferInstance
  -- the iterated conditional expectations, centred
  set u : ℕ → X → ℝ := fun n x => (∫ y, φ y ∂(iterKernel P n x)) - c₀ with hu
  have hum : ∀ n, Measurable (u n) := by
    intro n
    exact ((hφ.stronglyMeasurable.integral_kernel
      (κ := iterKernel P n)).measurable).sub measurable_const
  -- the geometric majorant
  set s : ℝ := max t (1/2) with hs
  have hs0 : 0 ≤ s := le_trans ht0 (le_max_left _ _)
  have hs1 : s < 1 := max_lt ht1 (by norm_num)
  have hts : t ≤ s := le_max_left _ _
  set a : ℕ → ℝ := fun n => 2 * B * (1 + R) * s ^ n with ha
  have hna : ∀ n, 0 ≤ a n := by
    intro n
    rw [ha]
    positivity
  have hasum : Summable a := by
    rw [ha]
    exact (summable_geometric_of_lt_one hs0 hs1).mul_left _
  have hbound : ∀ n x, |u n x| ≤ a n := by
    intro n x
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : ∫ y, φ y ∂(iterKernel P 0 x) = φ x := by
        rw [iterKernel_zero, Kernel.id_apply, integral_dirac' _ _ hφ.stronglyMeasurable]
      have hle : |u 0 x| ≤ 2 * B := by
        rw [hu]
        simp only [h0]
        calc |φ x - c₀| ≤ |φ x| + |c₀| := abs_sub _ _
          _ ≤ 2 * B := by linarith [hB x, hc₀B]
      refine le_trans hle ?_
      simp only [ha, pow_zero, mul_one]
      nlinarith
    · have hstep := abs_integral_sub_le_tvDist_of_bounded (iterKernel P n x) π φ hφ B hB0 hB
      have htv := hrate x n hn
      have h1 : |u n x| ≤ 2 * B * (R * t ^ n) := by
        rw [hu]
        refine le_trans hstep ?_
        exact mul_le_mul_of_nonneg_left htv (by positivity)
      refine le_trans h1 ?_
      simp only [ha]
      have h2 : t ^ n ≤ s ^ n := by gcongr
      nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 * B * R),
        pow_nonneg hs0 n, pow_nonneg ht0 n]
  have hsummable : ∀ x, Summable (fun n => u n x) := by
    intro x
    exact hasum.of_norm_bounded (fun n => by simpa using hbound n x)
  have hsummableN : ∀ x, Summable (fun n => ‖u n x‖) := by
    intro x
    exact hasum.of_norm_bounded (fun n => by simpa using hbound n x)
  -- the Poisson solution
  refine ⟨fun x => ∑' n, u n x, ?_, ⟨∑' n, a n, ?_⟩, ?_⟩
  · -- measurability, as a pointwise limit of partial sums
    have hpart : ∀ N : ℕ, Measurable (fun x => ∑ i ∈ Finset.range N, u i x) :=
      fun N => Finset.measurable_sum _ (fun i _ => hum i)
    refine measurable_of_tendsto_metrizable hpart (tendsto_pi_nhds.mpr (fun x => ?_))
    exact ((hsummable x).hasSum).tendsto_sum_nat
  · -- uniform bound
    intro x
    have hnb : ∀ n, ‖u n x‖ ≤ a n := fun n => by simpa using hbound n x
    have h1 : ‖∑' n, u n x‖ ≤ ∑' n, ‖u n x‖ := norm_tsum_le_tsum_norm (hsummableN x)
    have h2 : ∑' n, ‖u n x‖ ≤ ∑' n, a n := (hsummableN x).tsum_le_tsum hnb hasum
    simpa [Real.norm_eq_abs] using le_trans h1 h2
  · -- the Poisson identity
    intro x
    have hcomm : ∀ n : ℕ, iterKernel P n ∘ₖ P = iterKernel P (n + 1) := by
      intro n
      induction n with
      | zero =>
          rw [iterKernel_zero, iterKernel_succ, iterKernel_zero, Kernel.id_comp, Kernel.comp_id]
      | succ k ih =>
          rw [iterKernel_succ, Kernel.comp_assoc, ih]
          rfl
    have hkerint : ∀ n : ℕ, Integrable (fun y => ∫ z, φ z ∂(iterKernel P n y)) (P x) := by
      intro n
      exact ⟨((hφ.stronglyMeasurable.integral_kernel
          (κ := iterKernel P n)).measurable).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := B) (ae_of_all _ (fun y => by
          simpa [Real.norm_eq_abs] using hIntBound (iterKernel P n y) inferInstance))⟩
    have hstep : ∀ n : ℕ, ∫ y, u n y ∂(P x) = u (n + 1) x := by
      intro n
      haveI : IsMarkovKernel (iterKernel P n ∘ₖ P) := Kernel.IsMarkovKernel.comp _ _
      have hint : Integrable φ ((iterKernel P n ∘ₖ P) x) :=
        hIntφ _ inferInstance
      have h1 : ∫ z, φ z ∂((iterKernel P n ∘ₖ P) x)
          = ∫ y, (∫ z, φ z ∂(iterKernel P n y)) ∂(P x) :=
        Kernel.integral_comp hint
      rw [hcomm n] at h1
      have h2 : ∫ y, u n y ∂(P x)
          = (∫ y, (∫ z, φ z ∂(iterKernel P n y)) ∂(P x)) - c₀ := by
        simp only [hu]
        rw [integral_sub (hkerint n) (integrable_const c₀)]
        simp
      rw [h2, ← h1, hu]
    -- exchange the integral and the series
    have hexch : ∫ y, (∑' n, u n y) ∂(P x) = ∑' n, ∫ y, u n y ∂(P x) := by
      refine integral_tsum (fun n => (hum n).aestronglyMeasurable) ?_
      have hle : ∀ n, ∫⁻ y, ‖u n y‖ₑ ∂(P x) ≤ ENNReal.ofReal (a n) := by
        intro n
        calc ∫⁻ y, ‖u n y‖ₑ ∂(P x) ≤ ∫⁻ _y : X, ENNReal.ofReal (a n) ∂(P x) := by
              refine lintegral_mono (fun y => ?_)
              rw [← ofReal_norm_eq_enorm]
              exact ENNReal.ofReal_le_ofReal (by simpa using hbound n y)
          _ = ENNReal.ofReal (a n) := by simp
      have hfin : ∑' n, ENNReal.ofReal (a n) ≠ ∞ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hna hasum]
        exact ENNReal.ofReal_ne_top
      exact ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) (lt_top_iff_ne_top.mpr hfin))
    rw [hexch]
    simp only [hstep]
    have hshift : ∑' n, u (n + 1) x = (∑' n, u n x) - u 0 x := by
      have h := (hsummable x).tsum_eq_zero_add
      linarith [h]
    rw [hshift]
    have h0 : u 0 x = φ x - c₀ := by
      rw [hu]
      simp only
      rw [iterKernel_zero, Kernel.id_apply, integral_dirac' _ _ hφ.stronglyMeasurable]
    rw [h0]
    ring

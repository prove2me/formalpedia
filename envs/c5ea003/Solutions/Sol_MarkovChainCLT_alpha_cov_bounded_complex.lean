-- Prove2me | solution 1 for MarkovChainCLT.alpha_cov_bounded_complex
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T08:56:23.695926+00:00
-- url     : https://prove2.me/submissions/cfdc43fc-5c28-48a1-9b35-6317b5790cba

import Theorems.Thm_MarkovChainCLT_alpha_cov_bounded
import Theorems.Thm_MarkovChainCLT_processSigma_le_of_measurable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Rescaled form of the bounded covariance inequality: separate bounds for the two
variables. -/
private theorem alpha_cov_bounded_aux (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ n, Measurable (Y n)) (n k : ℕ) (U V : Ω → ℝ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + n))] V)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hUb : ∀ ω, |U ω| ≤ A) (hVb : ∀ ω, |V ω| ≤ B) :
    |cov[U, V; P]| ≤ 4 * A * B * alphaMixingCoef P Y n := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hU0 : U = fun _ => (0 : ℝ) := by
      funext ω
      have := hUb ω
      rw [← hA0] at this
      exact abs_nonpos_iff.mp this
    rw [hU0]
    have : cov[fun _ => (0 : ℝ), V; P] = 0 := covariance_const_left 0
    rw [this, ← hA0]
    simp
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · have hV0 : V = fun _ => (0 : ℝ) := by
      funext ω
      have := hVb ω
      rw [← hB0] at this
      exact abs_nonpos_iff.mp this
    rw [hV0]
    have : cov[U, fun _ => (0 : ℝ); P] = 0 := covariance_const_right 0
    rw [this, ← hB0]
    simp
  · set U' : Ω → ℝ := fun ω => A⁻¹ * U ω with hU'
    set V' : Ω → ℝ := fun ω => B⁻¹ * V ω with hV'
    have hU'meas : Measurable[processSigma Y (Set.Iic k)] U' := by
      exact (measurable_const.mul hU : Measurable[processSigma Y (Set.Iic k)] _)
    have hV'meas : Measurable[processSigma Y (Set.Ici (k + n))] V' := by
      exact (measurable_const.mul hV : Measurable[processSigma Y (Set.Ici (k + n))] _)
    have hU'b : ∀ ω, |U' ω| ≤ 1 := by
      intro ω
      rw [hU', abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ A⁻¹)]
      rw [inv_mul_le_iff₀ hApos]
      simpa using hUb ω
    have hV'b : ∀ ω, |V' ω| ≤ 1 := by
      intro ω
      rw [hV', abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ B⁻¹)]
      rw [inv_mul_le_iff₀ hBpos]
      simpa using hVb ω
    have hmain := MarkovChainCLT.alpha_cov_bounded P Y hY n k U' V' hU'meas hV'meas 1
      zero_le_one hU'b hV'b
    have hcov : cov[U', V'; P] = A⁻¹ * B⁻¹ * cov[U, V; P] := by
      rw [hU', hV', covariance_const_mul_left, covariance_const_mul_right, ← mul_assoc]
    rw [hcov] at hmain
    have habs : |A⁻¹ * B⁻¹ * cov[U, V; P]| = A⁻¹ * B⁻¹ * |cov[U, V; P]| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ A⁻¹),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ B⁻¹)]
    rw [habs] at hmain
    have hstep : A * B * (A⁻¹ * B⁻¹ * |cov[U, V; P]|)
        ≤ A * B * (4 * 1 ^ 2 * alphaMixingCoef P Y n) :=
      mul_le_mul_of_nonneg_left hmain (by positivity)
    calc |cov[U, V; P]| = A * B * (A⁻¹ * B⁻¹ * |cov[U, V; P]|) := by
          field_simp
      _ ≤ A * B * (4 * 1 ^ 2 * alphaMixingCoef P Y n) := hstep
      _ = 4 * A * B * alphaMixingCoef P Y n := by ring


/-- Complex-valued form of the bounded covariance inequality under strong mixing. -/
theorem solution {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ n, Measurable (Y n)) (n k : ℕ) (U V : Ω → ℂ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + n))] V)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hUb : ∀ ω, ‖U ω‖ ≤ A) (hVb : ∀ ω, ‖V ω‖ ≤ B) :
    ‖(∫ ω, U ω * V ω ∂P) - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P)‖
      ≤ 16 * A * B * alphaMixingCoef P Y n := by
  classical
  set u1 : Ω → ℝ := fun ω => (U ω).re with hu1def
  set u2 : Ω → ℝ := fun ω => (U ω).im with hu2def
  set v1 : Ω → ℝ := fun ω => (V ω).re with hv1def
  set v2 : Ω → ℝ := fun ω => (V ω).im with hv2def
  have hu1 : Measurable[processSigma Y (Set.Iic k)] u1 := Complex.measurable_re.comp hU
  have hu2 : Measurable[processSigma Y (Set.Iic k)] u2 := Complex.measurable_im.comp hU
  have hv1 : Measurable[processSigma Y (Set.Ici (k + n))] v1 := Complex.measurable_re.comp hV
  have hv2 : Measurable[processSigma Y (Set.Ici (k + n))] v2 := Complex.measurable_im.comp hV
  have hUm : Measurable U := hU.mono (processSigma_le_of_measurable Y hY _) le_rfl
  have hVm : Measurable V := hV.mono (processSigma_le_of_measurable Y hY _) le_rfl
  have hu1m : Measurable u1 := Complex.measurable_re.comp hUm
  have hu2m : Measurable u2 := Complex.measurable_im.comp hUm
  have hv1m : Measurable v1 := Complex.measurable_re.comp hVm
  have hv2m : Measurable v2 := Complex.measurable_im.comp hVm
  have hu1b : ∀ ω, |u1 ω| ≤ A := fun ω => (Complex.abs_re_le_norm _).trans (hUb ω)
  have hu2b : ∀ ω, |u2 ω| ≤ A := fun ω => (Complex.abs_im_le_norm _).trans (hUb ω)
  have hv1b : ∀ ω, |v1 ω| ≤ B := fun ω => (Complex.abs_re_le_norm _).trans (hVb ω)
  have hv2b : ∀ ω, |v2 ω| ≤ B := fun ω => (Complex.abs_im_le_norm _).trans (hVb ω)
  -- the four covariance bounds
  have hcov11 := alpha_cov_bounded_aux P Y hY n k u1 v1 hu1 hv1 A B hA hB hu1b hv1b
  have hcov22 := alpha_cov_bounded_aux P Y hY n k u2 v2 hu2 hv2 A B hA hB hu2b hv2b
  have hcov12 := alpha_cov_bounded_aux P Y hY n k u1 v2 hu1 hv2 A B hA hB hu1b hv2b
  have hcov21 := alpha_cov_bounded_aux P Y hY n k u2 v1 hu2 hv1 A B hA hB hu2b hv1b
  -- integrability
  have hUint : Integrable U P :=
    (MemLp.of_bound (p := 1) hUm.aestronglyMeasurable A (Filter.Eventually.of_forall hUb)).integrable
      le_rfl
  have hVint : Integrable V P :=
    (MemLp.of_bound (p := 1) hVm.aestronglyMeasurable B (Filter.Eventually.of_forall hVb)).integrable
      le_rfl
  have hUVint : Integrable (fun ω => U ω * V ω) P := by
    refine (MemLp.of_bound (p := 1) (hUm.mul hVm).aestronglyMeasurable (A * B)
      (Filter.Eventually.of_forall fun ω => ?_)).integrable le_rfl
    rw [norm_mul]
    exact mul_le_mul (hUb ω) (hVb ω) (norm_nonneg _) hA
  have hmemLp : ∀ (f : Ω → ℝ) (C : ℝ), Measurable f → (∀ ω, |f ω| ≤ C) → MemLp f 2 P := by
    intro f C hf hfb
    exact MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => hfb ω)
  have hu1L : MemLp u1 2 P := hmemLp u1 A hu1m hu1b
  have hu2L : MemLp u2 2 P := hmemLp u2 A hu2m hu2b
  have hv1L : MemLp v1 2 P := hmemLp v1 B hv1m hv1b
  have hv2L : MemLp v2 2 P := hmemLp v2 B hv2m hv2b
  have hprod : ∀ (f g : Ω → ℝ) (C D : ℝ), Measurable f → Measurable g →
      (∀ ω, |f ω| ≤ C) → (∀ ω, |g ω| ≤ D) → Integrable (fun ω => f ω * g ω) P := by
    intro f g C D hf hg hfb hgb
    refine (MemLp.of_bound (p := 1) (hf.mul hg).aestronglyMeasurable (C * D)
      (Filter.Eventually.of_forall fun ω => ?_)).integrable le_rfl
    have h1 : |f ω * g ω| = |f ω| * |g ω| := abs_mul _ _
    have h2 : |f ω| * |g ω| ≤ C * D :=
      mul_le_mul (hfb ω) (hgb ω) (abs_nonneg _) ((abs_nonneg _).trans (hfb ω))
    simpa [Real.norm_eq_abs, h1] using h2
  have h11 : Integrable (fun ω => u1 ω * v1 ω) P := hprod u1 v1 A B hu1m hv1m hu1b hv1b
  have h22 : Integrable (fun ω => u2 ω * v2 ω) P := hprod u2 v2 A B hu2m hv2m hu2b hv2b
  have h12 : Integrable (fun ω => u1 ω * v2 ω) P := hprod u1 v2 A B hu1m hv2m hu1b hv2b
  have h21 : Integrable (fun ω => u2 ω * v1 ω) P := hprod u2 v1 A B hu2m hv1m hu2b hv1b
  -- real and imaginary parts of the integrals
  have hUVre : (∫ ω, U ω * V ω ∂P).re
      = (∫ ω, u1 ω * v1 ω ∂P) - (∫ ω, u2 ω * v2 ω ∂P) := by
    have h := Complex.reCLM.integral_comp_comm hUVint
    simp only [Complex.reCLM_apply] at h
    rw [← h]
    simp only [Complex.mul_re, hu1def, hu2def, hv1def, hv2def]
    exact integral_sub h11 h22
  have hUVim : (∫ ω, U ω * V ω ∂P).im
      = (∫ ω, u1 ω * v2 ω ∂P) + (∫ ω, u2 ω * v1 ω ∂P) := by
    have h := Complex.imCLM.integral_comp_comm hUVint
    simp only [Complex.imCLM_apply] at h
    rw [← h]
    simp only [Complex.mul_im, hu1def, hu2def, hv1def, hv2def]
    exact integral_add h12 h21
  have hUre : (∫ ω, U ω ∂P).re = ∫ ω, u1 ω ∂P := by
    have h := Complex.reCLM.integral_comp_comm hUint
    simp only [Complex.reCLM_apply] at h
    exact h.symm
  have hUim : (∫ ω, U ω ∂P).im = ∫ ω, u2 ω ∂P := by
    have h := Complex.imCLM.integral_comp_comm hUint
    simp only [Complex.imCLM_apply] at h
    exact h.symm
  have hVre : (∫ ω, V ω ∂P).re = ∫ ω, v1 ω ∂P := by
    have h := Complex.reCLM.integral_comp_comm hVint
    simp only [Complex.reCLM_apply] at h
    exact h.symm
  have hVim : (∫ ω, V ω ∂P).im = ∫ ω, v2 ω ∂P := by
    have h := Complex.imCLM.integral_comp_comm hVint
    simp only [Complex.imCLM_apply] at h
    exact h.symm
  -- the covariances as integral differences
  have hc11 : cov[u1, v1; P] = (∫ ω, u1 ω * v1 ω ∂P) - (∫ ω, u1 ω ∂P) * (∫ ω, v1 ω ∂P) := by
    simpa [Pi.mul_apply] using covariance_eq_sub hu1L hv1L
  have hc22 : cov[u2, v2; P] = (∫ ω, u2 ω * v2 ω ∂P) - (∫ ω, u2 ω ∂P) * (∫ ω, v2 ω ∂P) := by
    simpa [Pi.mul_apply] using covariance_eq_sub hu2L hv2L
  have hc12 : cov[u1, v2; P] = (∫ ω, u1 ω * v2 ω ∂P) - (∫ ω, u1 ω ∂P) * (∫ ω, v2 ω ∂P) := by
    simpa [Pi.mul_apply] using covariance_eq_sub hu1L hv2L
  have hc21 : cov[u2, v1; P] = (∫ ω, u2 ω * v1 ω ∂P) - (∫ ω, u2 ω ∂P) * (∫ ω, v1 ω ∂P) := by
    simpa [Pi.mul_apply] using covariance_eq_sub hu2L hv1L
  set D : ℂ := (∫ ω, U ω * V ω ∂P) - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P) with hD
  have hDre : D.re = cov[u1, v1; P] - cov[u2, v2; P] := by
    rw [hD, Complex.sub_re, Complex.mul_re, hUVre, hUre, hUim, hVre, hVim, hc11, hc22]
    ring
  have hDim : D.im = cov[u1, v2; P] + cov[u2, v1; P] := by
    rw [hD, Complex.sub_im, Complex.mul_im, hUVim, hUre, hUim, hVre, hVim, hc12, hc21]
    ring
  have habs1 : |D.re| ≤ 4 * A * B * alphaMixingCoef P Y n + 4 * A * B * alphaMixingCoef P Y n := by
    rw [hDre]
    calc |cov[u1, v1; P] - cov[u2, v2; P]| ≤ |cov[u1, v1; P]| + |cov[u2, v2; P]| :=
          abs_sub _ _
      _ ≤ _ := add_le_add hcov11 hcov22
  have habs2 : |D.im| ≤ 4 * A * B * alphaMixingCoef P Y n + 4 * A * B * alphaMixingCoef P Y n := by
    rw [hDim]
    calc |cov[u1, v2; P] + cov[u2, v1; P]| ≤ |cov[u1, v2; P]| + |cov[u2, v1; P]| :=
          abs_add_le _ _
      _ ≤ _ := add_le_add hcov12 hcov21
  calc ‖D‖ ≤ |D.re| + |D.im| := Complex.norm_le_abs_re_add_abs_im D
    _ ≤ (4 * A * B * alphaMixingCoef P Y n + 4 * A * B * alphaMixingCoef P Y n)
        + (4 * A * B * alphaMixingCoef P Y n + 4 * A * B * alphaMixingCoef P Y n) :=
      add_le_add habs1 habs2
    _ = 16 * A * B * alphaMixingCoef P Y n := by ring


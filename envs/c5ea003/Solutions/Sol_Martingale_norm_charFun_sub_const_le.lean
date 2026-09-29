-- Prove2me | solution 1 for Martingale.norm_charFun_sub_const_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T19:32:08.15946+00:00
-- url     : https://prove2.me/submissions/34682146-a850-421d-b92d-aeb52668d90d

import Theorems.Thm_Martingale_expectation_prod_one_add
import Theorems.Thm_Martingale_norm_prod_one_add_I_mul_bounds
import Theorems.Thm_Martingale_norm_exp_sum_div_prod_sub_gaussian_le

set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (Z : ℕ → Ω → ℝ) (hmeas : ∀ k, Measurable (Z k))
    (hadapt : ∀ k, Measurable[ℱ k] (Z k))
    (hint : ∀ k, Integrable (Z k) P)
    (hmds : ∀ k, P[Z (k + 1) | ℱ k] =ᵐ[P] 0)
    (hcent : ∫ ω, Z 0 ω ∂P = 0)
    (C : ℝ) (hbdd : ∀ k ω, |Z k ω| ≤ C)
    (θ M : ℝ) (n : ℕ)
    (hvar : ∀ ω, ∑ k ∈ Finset.range n, Z k ω ^ 2 ≤ M)
    (hsmall : ∀ k ∈ Finset.range n, ∀ ω, |θ * Z k ω| ≤ 1)
    (c : ℂ) :
    ‖(∫ ω, Complex.exp (Complex.I * θ * ((∑ k ∈ Finset.range n, Z k ω : ℝ) : ℂ)) ∂P) - c‖
      ≤ Real.exp (θ ^ 2 * M / 2) *
        ∫ ω, ((∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3)
          + ‖((Real.exp (-(θ ^ 2 * ∑ k ∈ Finset.range n, Z k ω ^ 2) / 2) : ℝ) : ℂ) - c‖) ∂P := by
  classical
  set Pi : Ω → ℂ := fun ω => ∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ)) with hPi
  set Ex : Ω → ℂ :=
    fun ω => Complex.exp (Complex.I * θ * ((∑ k ∈ Finset.range n, Z k ω : ℝ) : ℂ)) with hEx
  set G : Ω → ℂ :=
    fun ω => ((Real.exp (-(θ ^ 2 * ∑ k ∈ Finset.range n, Z k ω ^ 2) / 2) : ℝ) : ℂ) with hG
  set K : ℝ := Real.exp (θ ^ 2 * M / 2) with hK
  have hKpos : 0 < K := Real.exp_pos _
  -- a helper: bounded measurable real functions are integrable
  have hIbdd : ∀ (g : Ω → ℝ) (B : ℝ), Measurable g → (∀ ω, |g ω| ≤ B) → Integrable g P := by
    intro g B hg hb
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const B).mono ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_trans (hb ω) (le_abs_self B)
  -- measurability
  have hmPi : Measurable Pi := by
    rw [hPi]
    refine Finset.measurable_prod _ (fun k _ => ?_)
    have := hmeas k
    fun_prop
  have hmsum : Measurable (fun ω => (∑ k ∈ Finset.range n, Z k ω : ℝ)) :=
    Finset.measurable_sum _ (fun k _ => hmeas k)
  have hmEx : Measurable Ex := by
    rw [hEx]
    have := hmsum
    fun_prop
  have hmsq : Measurable (fun ω => (∑ k ∈ Finset.range n, Z k ω ^ 2 : ℝ)) :=
    Finset.measurable_sum _ (fun k _ => (hmeas k).pow_const 2)
  have hmG : Measurable G := by
    rw [hG]
    have := hmsq
    fun_prop
  -- `1 ≤ ‖Pi‖ ≤ K`
  have hge1 : ∀ ω, 1 ≤ ‖Pi ω‖ := fun ω =>
    (Martingale.norm_prod_one_add_I_mul_bounds Z θ n ω).1
  have hleK : ∀ ω, ‖Pi ω‖ ≤ K := by
    intro ω
    have h2 := (Martingale.norm_prod_one_add_I_mul_bounds Z θ n ω).2
    have hmono : Real.exp (θ ^ 2 * ∑ k ∈ Finset.range n, Z k ω ^ 2) ≤ Real.exp (θ ^ 2 * M) := by
      refine Real.exp_le_exp.mpr ?_
      exact mul_le_mul_of_nonneg_left (hvar ω) (sq_nonneg θ)
    have hKsq : K ^ 2 = Real.exp (θ ^ 2 * M) := by
      rw [hK, ← Real.exp_nat_mul]
      congr 1
      ring
    nlinarith [norm_nonneg (Pi ω), hKpos, h2, hmono]
  have hne : ∀ ω, Pi ω ≠ 0 := by
    intro ω h
    have := hge1 ω
    rw [h, norm_zero] at this
    linarith
  -- integrability of the pieces
  have hIEx : Integrable Ex P := by
    refine ⟨hmEx.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const (1:ℝ)).mono ?_
    filter_upwards with ω
    have hcast : Complex.I * (θ:ℂ) * ((∑ k ∈ Finset.range n, Z k ω : ℝ) : ℂ)
        = ((θ * ∑ k ∈ Finset.range n, Z k ω : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hone : ‖Ex ω‖ = 1 := by
      show ‖Complex.exp (Complex.I * (θ:ℂ) * ((∑ k ∈ Finset.range n, Z k ω : ℝ) : ℂ))‖ = 1
      rw [hcast, Complex.norm_exp_ofReal_mul_I]
    rw [hone, norm_one]
  have hIPi : Integrable Pi P := by
    refine ⟨hmPi.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const K).mono ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg hKpos.le]
    exact hleK ω
  -- `∫ Pi = 1`, so subtracting `c` is the same as subtracting `c * Pi`
  have hPi1 : ∫ ω, Pi ω ∂P = 1 :=
    Martingale.expectation_prod_one_add P ℱ Z hmeas hadapt hint hmds hcent C hbdd θ n
  have hstep1 : (∫ ω, Ex ω ∂P) - c = ∫ ω, (Ex ω - c * Pi ω) ∂P := by
    rw [integral_sub hIEx (hIPi.const_mul c), integral_const_mul, hPi1, mul_one]
  -- the pathwise bound on the integrand
  have hmaj : ∀ ω, ‖Ex ω - c * Pi ω‖
      ≤ K * ((∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3) + ‖G ω - c‖) := by
    intro ω
    have hfac : Ex ω - c * Pi ω = Pi ω * (Ex ω / Pi ω - c) := by
      rw [mul_sub, mul_div_cancel₀ _ (hne ω)]
      ring
    have hJ2 : ‖Ex ω / Pi ω - G ω‖ ≤ ∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3 :=
      Martingale.norm_exp_sum_div_prod_sub_gaussian_le Z θ n ω (fun k hk => hsmall k hk ω)
    have htri : ‖Ex ω / Pi ω - c‖
        ≤ (∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3) + ‖G ω - c‖ := by
      calc ‖Ex ω / Pi ω - c‖ = ‖(Ex ω / Pi ω - G ω) + (G ω - c)‖ := by ring_nf
        _ ≤ ‖Ex ω / Pi ω - G ω‖ + ‖G ω - c‖ := norm_add_le _ _
        _ ≤ (∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3) + ‖G ω - c‖ := by linarith
    rw [hfac, norm_mul]
    exact mul_le_mul (hleK ω) htri (norm_nonneg _) hKpos.le
  -- integrability of the majorant
  have hmcube : Measurable (fun ω => ∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3) := by
    refine Finset.measurable_sum _ (fun k _ => ?_)
    have := hmeas k
    fun_prop
  have hmGc : Measurable (fun ω => ‖G ω - c‖) := (hmG.sub measurable_const).norm
  have hIcube : Integrable (fun ω => ∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3) P := by
    refine hIbdd _ (n * (|θ| * C) ^ 3) hmcube (fun ω => ?_)
    have hC0 : (0:ℝ) ≤ C := le_trans (abs_nonneg _) (hbdd 0 ω)
    have hterm : ∀ k, |θ * Z k ω| ^ 3 ≤ (|θ| * C) ^ 3 := by
      intro k
      have h1 : |θ * Z k ω| ≤ |θ| * C := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbdd k ω) (abs_nonneg θ)
      have h0 : (0:ℝ) ≤ |θ * Z k ω| := abs_nonneg _
      gcongr
    have hnn : (0:ℝ) ≤ ∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3 :=
      Finset.sum_nonneg (fun k _ => by positivity)
    rw [abs_of_nonneg hnn]
    calc ∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3
        ≤ ∑ _k ∈ Finset.range n, (|θ| * C) ^ 3 :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = n * (|θ| * C) ^ 3 := by simp [mul_comm]
  have hIGc : Integrable (fun ω => ‖G ω - c‖) P := by
    refine hIbdd _ (1 + ‖c‖) hmGc (fun ω => ?_)
    have hGle : ‖G ω‖ ≤ 1 := by
      rw [hG, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_one_iff.mpr ?_
      have : (0:ℝ) ≤ θ ^ 2 * ∑ k ∈ Finset.range n, Z k ω ^ 2 :=
        mul_nonneg (sq_nonneg θ) (Finset.sum_nonneg (fun k _ => sq_nonneg _))
      linarith
    rw [abs_of_nonneg (norm_nonneg _)]
    exact le_trans (norm_sub_le _ _) (by linarith)
  have hImaj : Integrable
      (fun ω => K * ((∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3) + ‖G ω - c‖)) P :=
    (hIcube.add hIGc).const_mul K
  have hIdiff : Integrable (fun ω => Ex ω - c * Pi ω) P := hIEx.sub (hIPi.const_mul c)
  -- assemble
  rw [hstep1]
  calc ‖∫ ω, (Ex ω - c * Pi ω) ∂P‖
      ≤ ∫ ω, ‖Ex ω - c * Pi ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, K * ((∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3) + ‖G ω - c‖) ∂P :=
        integral_mono hIdiff.norm hImaj hmaj
    _ = K * ∫ ω, ((∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3) + ‖G ω - c‖) ∂P :=
        integral_const_mul _ _

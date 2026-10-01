-- Prove2me | solution 1 for RybinAI2026.P01.psi_sqrt_trigonometric_integral
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:38:36.251007+00:00
-- url     : https://prove2.me/submissions/07cb3048-443c-4d8d-acb4-b54995541adc

import Mathlib
open Set MeasureTheory
noncomputable section
namespace APsi
lemma denom_pos (q : ℝ) (hq : 0 < q) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (Real.pi / 2)) : 0 < q * Real.cos θ + Real.sin θ := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc (show θ ∈ Icc (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith [hθ.1, Real.pi_pos],hθ.2⟩)
  by_cases hz : θ = 0
  · simp [hz,hq]
  · have hp := Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne hθ.1 (Ne.symm hz)) (by linarith [hθ.2, Real.pi_pos])
    positivity
lemma subst_deriv (q : ℝ) (hq : 0 < q) {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    HasDerivAt (fun θ => Real.sin θ / (q * Real.cos θ + Real.sin θ))
      (q / (q * Real.cos θ + Real.sin θ)^2) θ := by
  convert (Real.hasDerivAt_sin θ).div
    (((Real.hasDerivAt_cos θ).const_mul q).add (Real.hasDerivAt_sin θ))
    (ne_of_gt (denom_pos q hq hθ)) using 1
  congr 1
  dsimp only [Pi.add_apply]
  nlinarith [congrArg (fun z : ℝ => q*z) (Real.sin_sq_add_cos_sq θ)]
lemma identity (q : ℝ) (hq : 0 < q) {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi/2)) :
    q * ((1 + (q^2-1)*(Real.sin θ/(q*Real.cos θ+Real.sin θ))^2)⁻¹ *
      (q/(q*Real.cos θ+Real.sin θ)^2)) =
      (1+(2/q)*Real.sin θ*Real.cos θ)⁻¹ := by
  have hd := ne_of_gt (denom_pos q hq hθ)
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc (show θ ∈ Icc (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith [hθ.1, Real.pi_pos],hθ.2⟩)
  have hp : 0 < q^2+2*q*Real.sin θ*Real.cos θ := by positivity
  have he : (q*Real.cos θ+Real.sin θ)^2+(q^2-1)*Real.sin θ^2 = q^2+2*q*Real.sin θ*Real.cos θ := by
    nlinarith [congrArg (fun z : ℝ => q^2*z) (Real.sin_sq_add_cos_sq θ)]
  field_simp
  rw [he]
  exact (div_eq_one_iff_eq (ne_of_gt hp)).2 (by ring)
end APsi

theorem solution (t : ℝ) (ht : 0 < t) :
    Real.sqrt t * (∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹) =
      ∫ θ in (0 : ℝ)..(Real.pi / 2),
        (1 + (2 / Real.sqrt t) * Real.sin θ * Real.cos θ)⁻¹ := by
  let q := Real.sqrt t
  have hq : 0 < q := Real.sqrt_pos.mpr ht
  have hq2 : q^2 = t := Real.sq_sqrt ht.le
  let φ : ℝ → ℝ := fun θ => Real.sin θ / (q*Real.cos θ+Real.sin θ)
  have hab : (0:ℝ) ≤ Real.pi/2 := by positivity
  have hφ : ContinuousOn φ (uIcc 0 (Real.pi/2)) := by
    rw [uIcc_of_le hab]
    exact Real.continuous_sin.continuousOn.div
      ((continuous_const.mul Real.continuous_cos).add Real.continuous_sin).continuousOn
      (fun θ hθ => ne_of_gt (APsi.denom_pos q hq hθ))
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := fun s : ℝ => (1+(t-1)*s^2)⁻¹) hφ
    (f' := fun θ => q/(q*Real.cos θ+Real.sin θ)^2)
    (fun θ hθ => APsi.subst_deriv q hq ⟨by simpa [min_eq_left hab] using hθ.1.le, by simpa [max_eq_right hab] using hθ.2.le⟩)
    (fun θ hθ => div_nonneg hq.le (sq_nonneg _))
  have h0 : φ 0 = 0 := by simp [φ]
  have h1 : φ (Real.pi/2) = 1 := by simp [φ]
  rw [h0,h1] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le hab] at hθ
  change q * _ = (1 + (2/q)*Real.sin θ*Real.cos θ)⁻¹
  simpa only [Function.comp_apply, φ, hq2] using APsi.identity q hq hθ

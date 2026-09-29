-- Prove2me | solution 1 for mme_CW_auxiliary_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-23T23:39:53.988595+00:00
-- url     : https://prove2.me/submissions/d51e1c88-f699-4412-9c0e-468d5c45a622

import Definitions.Def_mme_CW_auxiliary_RHS

open MME Real

theorem solution (tau₁ tau₂ : ℝ) (hτ : tau₁ ≤ tau₂) :
    auxiliaryRHS 6 tau₁ cw2376_a cw2376_b cw2376_c cw2376_d ≤
      auxiliaryRHS 6 tau₂ cw2376_a cw2376_b cw2376_c cw2376_d := by
  have ha : 0 < cw2376_a := by norm_num [cw2376_a]
  have hb : 0 < cw2376_b := by norm_num [cw2376_b]
  have hc : 0 < cw2376_c := by norm_num [cw2376_c]
  have hd : 0 < cw2376_d := by norm_num [cw2376_d]
  have hs₁ : 0 < 2 * cw2376_a + 2 * cw2376_b + cw2376_c := by linarith
  have hs₂ : 0 < 2 * cw2376_b + 2 * cw2376_d := by linarith
  have hs₃ : 0 < 2 * cw2376_c + cw2376_d := by linarith
  have hs₄ : 0 < 2 * cw2376_b := by linarith
  have hden :
      0 <
        (2 * cw2376_a + 2 * cw2376_b + cw2376_c) ^
              (2 * cw2376_a + 2 * cw2376_b + cw2376_c) *
            (2 * cw2376_b + 2 * cw2376_d) ^ (2 * cw2376_b + 2 * cw2376_d) *
          (2 * cw2376_c + cw2376_d) ^ (2 * cw2376_c + cw2376_d) *
        (2 * cw2376_b) ^ (2 * cw2376_b) * cw2376_a ^ cw2376_a := by
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (rpow_pos_of_pos hs₁ _) (rpow_pos_of_pos hs₂ _))
          (rpow_pos_of_pos hs₃ _))
        (rpow_pos_of_pos hs₄ _))
      (rpow_pos_of_pos ha _)
  unfold auxiliaryRHS
  apply (div_le_div_iff_of_pos_right hden).2
  have h₁ :
      (12 : ℝ) ^ (6 * tau₁ * cw2376_b) ≤
        (12 : ℝ) ^ (6 * tau₂ * cw2376_b) := by
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have h₂ :
      (38 : ℝ) ^ (3 * tau₁ * cw2376_c) ≤
        (38 : ℝ) ^ (3 * tau₂ * cw2376_c) := by
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hx :
      (6 : ℝ) ^ (3 * tau₁) ≤ (6 : ℝ) ^ (3 * tau₂) := by
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hcentral :
      4 * (6 : ℝ) ^ (3 * tau₁) * ((6 : ℝ) ^ (3 * tau₁) + 2) ≤
        4 * (6 : ℝ) ^ (3 * tau₂) * ((6 : ℝ) ^ (3 * tau₂) + 2) := by
    have hx₁ : 0 < (6 : ℝ) ^ (3 * tau₁) := by positivity
    have hx₂ : 0 < (6 : ℝ) ^ (3 * tau₂) := by positivity
    nlinarith
  have h₃ :
      (4 * (6 : ℝ) ^ (3 * tau₁) * ((6 : ℝ) ^ (3 * tau₁) + 2)) ^ cw2376_d ≤
        (4 * (6 : ℝ) ^ (3 * tau₂) * ((6 : ℝ) ^ (3 * tau₂) + 2)) ^ cw2376_d := by
    apply rpow_le_rpow (by positivity) hcentral
    exact hd.le
  norm_num only [Nat.cast_ofNat, Nat.cast_pow]
  have h₁₂ := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  exact mul_le_mul h₁₂ h₃ (by positivity) (by positivity)

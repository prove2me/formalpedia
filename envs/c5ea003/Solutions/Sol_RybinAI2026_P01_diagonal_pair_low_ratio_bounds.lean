-- Prove2me | solution 1 for RybinAI2026.P01.diagonal_pair_low_ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T00:48:00.993026+00:00
-- url     : https://prove2.me/submissions/bbea887b-4948-407b-9c4f-8ae22b83c8e6

import Mathlib

theorem solution (G : ℝ → ℝ) (hGpos : ∀ t, 0 < t → 0 < G t)
    (hGmono : MonotoneOn G (Set.Ioi 0))
    (x y T : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (hT : 0 < T) (hxy : x + y ≤ 1) :
    (Real.sqrt (x * (1 - y)) *
        (G T / G (T / (x / (1 - y))))) ^ 2 ≤ x * (1 - y) ∧
    (Real.sqrt (y * (1 - x)) *
        (G (1 / T) / G (1 / ((y / (1 - x)) * T)))) ^ 2 ≤ y * (1 - x) := by
  have hxden : 0 < 1 - y := sub_pos.mpr hy1
  have hyden : 0 < 1 - x := sub_pos.mpr hx1
  have hα : 0 < x / (1 - y) := div_pos hx0 hxden
  have hβ : 0 < y / (1 - x) := div_pos hy0 hyden
  have hαle : x / (1 - y) ≤ 1 := (div_le_iff₀ hxden).2 (by linarith)
  have hβle : y / (1 - x) ≤ 1 := (div_le_iff₀ hyden).2 (by linarith)
  have hTa : 0 < T / (x / (1 - y)) := div_pos hT hα
  have hTb : 0 < (y / (1 - x)) * T := mul_pos hβ hT
  have hTle : T ≤ T / (x / (1 - y)) :=
    (le_div_iff₀ hα).2 (by nlinarith [mul_nonneg hT.le (sub_nonneg.mpr hαle)])
  have hβT : (y / (1 - x)) * T ≤ T := by
    calc
      (y / (1 - x)) * T ≤ 1 * T := mul_le_mul_of_nonneg_right hβle hT.le
      _ = T := by ring
  have hInvle : 1 / T ≤ 1 / ((y / (1 - x)) * T) := by
    simpa only [one_div] using (inv_le_inv₀ hT hTb).2 hβT
  have hratio₁ : G T / G (T / (x / (1 - y))) ≤ 1 := by
    apply (div_le_iff₀ (hGpos _ hTa)).2
    simpa only [one_mul] using hGmono (Set.mem_Ioi.mpr hT) (Set.mem_Ioi.mpr hTa) hTle
  have hratio₂ : G (1 / T) / G (1 / ((y / (1 - x)) * T)) ≤ 1 := by
    have hden : 0 < 1 / ((y / (1 - x)) * T) := one_div_pos.mpr hTb
    apply (div_le_iff₀ (hGpos _ hden)).2
    simpa only [one_mul] using
      hGmono (Set.mem_Ioi.mpr (one_div_pos.mpr hT)) (Set.mem_Ioi.mpr hden) hInvle
  have hA0 : 0 ≤ Real.sqrt (x * (1 - y)) := Real.sqrt_nonneg _
  have hB0 : 0 ≤ Real.sqrt (y * (1 - x)) := Real.sqrt_nonneg _
  have hA2 : Real.sqrt (x * (1 - y)) ^ 2 = x * (1 - y) :=
    Real.sq_sqrt (le_of_lt (mul_pos hx0 hxden))
  have hB2 : Real.sqrt (y * (1 - x)) ^ 2 = y * (1 - x) :=
    Real.sq_sqrt (le_of_lt (mul_pos hy0 hyden))
  have hfirst : Real.sqrt (x * (1 - y)) *
      (G T / G (T / (x / (1 - y)))) ≤ Real.sqrt (x * (1 - y)) :=
    (mul_le_mul_of_nonneg_left hratio₁ hA0).trans_eq (by ring)
  have hsecond : Real.sqrt (y * (1 - x)) *
      (G (1 / T) / G (1 / ((y / (1 - x)) * T))) ≤ Real.sqrt (y * (1 - x)) :=
    (mul_le_mul_of_nonneg_left hratio₂ hB0).trans_eq (by ring)
  have hr₁ : 0 ≤ Real.sqrt (x * (1 - y)) *
      (G T / G (T / (x / (1 - y)))) :=
    mul_nonneg hA0 (div_nonneg (le_of_lt (hGpos _ hT)) (le_of_lt (hGpos _ hTa)))
  have hr₂ : 0 ≤ Real.sqrt (y * (1 - x)) *
      (G (1 / T) / G (1 / ((y / (1 - x)) * T))) :=
    mul_nonneg hB0 (div_nonneg (le_of_lt (hGpos _ (one_div_pos.mpr hT)))
      (le_of_lt (hGpos _ (one_div_pos.mpr hTb))))
  constructor
  · calc
      _ ≤ Real.sqrt (x * (1 - y)) ^ 2 := (sq_le_sq₀ hr₁ hA0).2 hfirst
      _ = x * (1 - y) := hA2
  · calc
      _ ≤ Real.sqrt (y * (1 - x)) ^ 2 := (sq_le_sq₀ hr₂ hB0).2 hsecond
      _ = y * (1 - x) := hB2

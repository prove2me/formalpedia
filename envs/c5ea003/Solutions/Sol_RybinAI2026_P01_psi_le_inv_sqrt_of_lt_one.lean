-- Prove2me | solution 1 for RybinAI2026.P01.psi_le_inv_sqrt_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T00:48:20.925711+00:00
-- url     : https://prove2.me/submissions/11511d6d-c6f2-4dc1-afcb-0be4ab8cc4aa

import Mathlib
import Theorems.Thm_RybinAI2026_P01_artanh_upper_slope

open MeasureTheory

theorem solution (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ ≤ 1 / Real.sqrt t := by
  let r := Real.sqrt (1 - t)
  have hr0 : 0 < 1 - t := sub_pos.mpr ht1
  have hr : 0 < r := Real.sqrt_pos.2 hr0
  have hr2 : r ^ 2 = 1 - t := Real.sq_sqrt (le_of_lt hr0)
  have hr1 : r < 1 := by nlinarith [hr2]
  have hminus_cont : ContinuousOn (fun u : ℝ => (1 - u)⁻¹) (Set.uIcc 0 r) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu
    rw [Set.uIcc_of_le hr.le] at hu
    exact ne_of_gt (sub_pos.mpr (lt_of_le_of_lt hu.2 hr1))
  have hplus_cont : ContinuousOn (fun u : ℝ => (1 + u)⁻¹) (Set.uIcc 0 r) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu
    rw [Set.uIcc_of_le hr.le] at hu
    exact ne_of_gt (by linarith [hu.1])
  have hprimitive :
      (∫ u in (0 : ℝ)..r, (1 - u ^ 2)⁻¹) = Real.artanh r := by
    have hp : IntervalIntegrable (fun u : ℝ => (1 - u)⁻¹) volume 0 r :=
      hminus_cont.intervalIntegrable
    have hq : IntervalIntegrable (fun u : ℝ => (1 + u)⁻¹) volume 0 r :=
      hplus_cont.intervalIntegrable
    have hsplit :
        (∫ u in (0 : ℝ)..r, (1 - u ^ 2)⁻¹) =
          (1 / 2) * (∫ u in (0 : ℝ)..r, (1 - u)⁻¹) +
            (1 / 2) * (∫ u in (0 : ℝ)..r, (1 + u)⁻¹) := by
      calc
        _ = ∫ u in (0 : ℝ)..r,
            (1 / 2) * (1 - u)⁻¹ + (1 / 2) * (1 + u)⁻¹ := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [Set.uIcc_of_le hr.le] at hu
          have h1 : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr (lt_of_le_of_lt hu.2 hr1))
          have h2 : 1 + u ≠ 0 := ne_of_gt (by linarith [hu.1])
          have h3 : 1 - u ^ 2 ≠ 0 := by
            apply ne_of_gt
            have h1p : 0 < 1 - u := sub_pos.mpr (lt_of_le_of_lt hu.2 hr1)
            have h2p : 0 < 1 + u := by linarith [hu.1]
            nlinarith [mul_pos h1p h2p]
          field_simp [h1, h2, h3]
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add (hp.const_mul (1 / 2))
            (hq.const_mul (1 / 2))]
          simp only [intervalIntegral.integral_const_mul]
    have hminus :
        (∫ u in (0 : ℝ)..r, (1 - u)⁻¹) = Real.log (1 / (1 - r)) := by
      calc
        _ = ∫ u in (0 : ℝ)..r, (fun x : ℝ => x⁻¹) (1 - 1 * u) := by
          apply intervalIntegral.integral_congr
          intro u hu
          ring
        _ = ∫ x in 1 - r..1, x⁻¹ := by
          simpa using (intervalIntegral.integral_comp_sub_mul
            (f := fun x : ℝ => x⁻¹) (a := (0 : ℝ)) (b := r) (c := (1 : ℝ))
            one_ne_zero (1 : ℝ))
        _ = _ := integral_inv_of_pos (by linarith [hr1]) zero_lt_one
    have hplus :
        (∫ u in (0 : ℝ)..r, (1 + u)⁻¹) = Real.log (1 + r) := by
      calc
        _ = ∫ u in (0 : ℝ)..r, (fun x : ℝ => x⁻¹) (1 + 1 * u) := by
          apply intervalIntegral.integral_congr
          intro u hu
          ring
        _ = ∫ x in 1..1 + r, x⁻¹ := by
          simpa using (intervalIntegral.integral_comp_add_mul
            (f := fun x : ℝ => x⁻¹) (a := (0 : ℝ)) (b := r) (c := (1 : ℝ))
            one_ne_zero (1 : ℝ))
        _ = _ := by
          simpa only [div_one] using integral_inv_of_pos zero_lt_one (by positivity)
    have hmem : r ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hr.le], hr1.le⟩
    have hlog1 : Real.log (1 / (1 - r)) = -Real.log (1 - r) := by
      rw [Real.log_div (by norm_num) (ne_of_gt (sub_pos.mpr hr1))]
      simp
    have hlog2 : Real.log ((1 + r) / (1 - r)) =
        Real.log (1 + r) - Real.log (1 - r) :=
      Real.log_div (ne_of_gt (by positivity)) (ne_of_gt (sub_pos.mpr hr1))
    calc
      _ = (1 / 2) * Real.log (1 / (1 - r)) + (1 / 2) * Real.log (1 + r) := by
        rw [hsplit, hminus, hplus]
      _ = (1 / 2) * Real.log ((1 + r) / (1 - r)) := by rw [hlog1, hlog2]; ring
      _ = Real.artanh r := (Real.artanh_eq_half_log hmem).symm
  have heval :
      (∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹) = r⁻¹ * Real.artanh r := by
    have htminus : t - 1 = -r ^ 2 := by nlinarith [hr2]
    calc
      _ = ∫ s in (0 : ℝ)..1, (1 - (r * s) ^ 2)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro s hs
        congr 1
        rw [htminus]
        ring
      _ = r⁻¹ • ∫ u in r * 0..r * 1, (1 - u ^ 2)⁻¹ := by
        rw [intervalIntegral.integral_comp_mul_left
          (f := fun u : ℝ => (1 - u ^ 2)⁻¹) hr.ne']
      _ = r⁻¹ * Real.artanh r := by simp [hprimitive]
  have hden : 0 < Real.sqrt (1 - r ^ 2) := by
    rw [show 1 - r ^ 2 = t by nlinarith [hr2]]
    exact Real.sqrt_pos.2 ht
  have hartanh := RybinAI2026.P01.artanh_upper_slope r hr.le hr1
  have hmul : Real.artanh r * Real.sqrt (1 - r ^ 2) ≤ r :=
    (le_div_iff₀ hden).1 hartanh
  have hratio : Real.artanh r / r ≤ 1 / Real.sqrt (1 - r ^ 2) :=
    (div_le_div_iff₀ hr hden).2 (by simpa using hmul)
  have hsqrt : Real.sqrt (1 - r ^ 2) = Real.sqrt t := by
    congr 1
    nlinarith [hr2]
  calc
    _ = r⁻¹ * Real.artanh r := heval
    _ = Real.artanh r / r := by ring
    _ ≤ 1 / Real.sqrt (1 - r ^ 2) := hratio
    _ = 1 / Real.sqrt t := by rw [hsqrt]

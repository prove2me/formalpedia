-- Prove2me | solution 1 for RybinAI2026.P01.diagonal_angle_sin_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T06:52:35.014807+00:00
-- url     : https://prove2.me/submissions/dfec9a44-e7fd-4a43-93c0-6a8819c9e5c5

import Mathlib
import Theorems.Thm_RybinAI2026_P01_diagonal_angle_integral_formula

open MeasureTheory

noncomputable section

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
    ∫ θ in (-Real.pi)..Real.pi,
      |Real.sin θ| / (a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2) =
        4 * ψ (a / b) / b := by
  let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
  let f : ℝ → ℝ := fun θ =>
    |Real.sin θ| / (a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2)
  let g : ℝ → ℝ := fun θ =>
    |Real.cos θ| / (b * Real.cos θ ^ 2 + a * Real.sin θ ^ 2)
  change (∫ θ in (-Real.pi)..Real.pi, f θ) = 4 * ψ (a / b) / b
  have hpoint (θ : ℝ) : f θ = g (Real.pi / 2 - θ) := by
    simp [f, g, Real.cos_sub, Real.sin_sub, Real.sin_pi_div_two,
      Real.cos_pi_div_two]
    <;> ring
  have hden (θ : ℝ) : 0 < b * Real.cos θ ^ 2 + a * Real.sin θ ^ 2 := by
    by_cases hc : Real.cos θ = 0
    · have hs : Real.sin θ ^ 2 = 1 := by
        nlinarith [Real.sin_sq_add_cos_sq θ]
      simpa [hc, hs] using ha
    · exact add_pos_of_pos_of_nonneg (mul_pos hb (sq_pos_of_ne_zero hc))
        (mul_nonneg ha.le (sq_nonneg _))
  have hgcont : Continuous g := by
    dsimp [g]
    have hd : Continuous (fun θ : ℝ =>
        b * Real.cos θ ^ 2 + a * Real.sin θ ^ 2) := by fun_prop
    exact Real.continuous_cos.abs.div hd (fun θ => ne_of_gt (hden θ))
  have hint (x y : ℝ) : IntervalIntegrable g volume x y :=
    hgcont.continuousOn.intervalIntegrable
  have hper : Function.Periodic g Real.pi := by
    intro θ
    dsimp [g]
    rw [Real.cos_add_pi, Real.sin_add_pi]
    simp only [abs_neg, neg_sq]
  have hbase : (∫ θ in -Real.pi..0, g θ) =
      ∫ θ in -(Real.pi / 2)..(Real.pi / 2), g θ := by
    convert hper.intervalIntegral_add_eq (-Real.pi) (-(Real.pi / 2)) using 1 <;> ring
  have hsecond : (∫ θ in Real.pi / 2..(3 * Real.pi / 2), g θ) =
      ∫ θ in -(Real.pi / 2)..(Real.pi / 2), g θ := by
    convert hper.intervalIntegral_add_eq (Real.pi / 2) (-(Real.pi / 2)) using 1 <;> ring
  have hfull : (∫ θ in -Real.pi..Real.pi, g θ) =
      2 * (∫ θ in -Real.pi..0, g θ) := by
    calc
      _ = (∫ θ in -Real.pi..0, g θ) +
          ∫ θ in 0..Real.pi, g θ :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hint (-Real.pi) 0) (hint 0 Real.pi)).symm
      _ = _ := by
        have hperFull : (∫ θ in (0 : ℝ)..Real.pi, g θ) =
            ∫ θ in -Real.pi..0, g θ := by
          simpa only [zero_add, neg_add_cancel] using
            hper.intervalIntegral_add_eq (0 : ℝ) (-Real.pi)
        rw [hperFull]
        ring
  have hshifted : (∫ θ in -(Real.pi / 2)..(3 * Real.pi / 2), g θ) =
      2 * (∫ θ in -(Real.pi / 2)..(Real.pi / 2), g θ) := by
    calc
      _ = (∫ θ in -(Real.pi / 2)..(Real.pi / 2), g θ) +
          ∫ θ in Real.pi / 2..(3 * Real.pi / 2), g θ :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hint (-(Real.pi / 2)) (Real.pi / 2))
          (hint (Real.pi / 2) (3 * Real.pi / 2))).symm
      _ = _ := by rw [hsecond]; ring
  have hperiodicRanges : (∫ θ in -Real.pi..Real.pi, g θ) =
      ∫ θ in -(Real.pi / 2)..(3 * Real.pi / 2), g θ := by
    rw [hfull, hbase, hshifted]
  have hquarter : (∫ θ in -Real.pi..Real.pi, f θ) =
      ∫ θ in -Real.pi..Real.pi, g (Real.pi / 2 - θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact hpoint θ
  have hsub : (∫ θ in -Real.pi..Real.pi, g (Real.pi / 2 - θ)) =
      ∫ θ in -(Real.pi / 2)..(3 * Real.pi / 2), g θ := by
    convert intervalIntegral.integral_comp_sub_left (f := g)
      (a := -Real.pi) (b := Real.pi) (Real.pi / 2) using 1 <;> ring
  calc
    _ = ∫ θ in -Real.pi..Real.pi, g (Real.pi / 2 - θ) := hquarter
    _ = ∫ θ in -(Real.pi / 2)..(3 * Real.pi / 2), g θ := hsub
    _ = ∫ θ in -Real.pi..Real.pi, g θ := hperiodicRanges.symm
    _ = 4 * ψ (a / b) / b := by
      simpa [g, ψ] using
        (RybinAI2026.P01.diagonal_angle_integral_formula b a hb ha)

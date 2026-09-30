-- Prove2me | solution 1 for RybinAI2026.P01.diagonal_angle_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T05:53:37.705926+00:00
-- url     : https://prove2.me/submissions/372d126f-5448-4bda-bce3-5ec8a1cb2be3

import Mathlib

noncomputable section

open MeasureTheory

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
    ∫ θ in (-Real.pi)..Real.pi, |Real.cos θ| / (a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2) =
      4 * ψ (b / a) / a := by
  let f : ℝ → ℝ := fun θ => |Real.cos θ| / (a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2)
  let g : ℝ → ℝ := fun s => (a + (b - a) * s ^ 2)⁻¹
  change (∫ θ in (-Real.pi)..Real.pi, f θ) = 4 * (∫ s in (0 : ℝ)..1,
    (1 + (b / a - 1) * s ^ 2)⁻¹) / a
  have hden (θ : ℝ) : 0 < a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2 := by
    by_cases hc : Real.cos θ = 0
    · have hs : Real.sin θ ^ 2 = 1 := by simpa [hc] using Real.sin_sq_add_cos_sq θ
      simpa [hc, hs] using hb
    · exact add_pos_of_pos_of_nonneg (mul_pos ha (sq_pos_of_ne_zero hc))
        (mul_nonneg hb.le (sq_nonneg _))
  have hfcont : Continuous f := by
    dsimp [f]
    have hq : Continuous (fun θ : ℝ => a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2) := by fun_prop
    exact (Real.continuous_cos.abs).div hq (fun θ => ne_of_gt (hden θ))
  have hperiod (θ : ℝ) : f (θ + Real.pi) = f θ := by
    dsimp [f]; rw [Real.cos_add_pi, Real.sin_add_pi]; simp only [abs_neg, neg_sq]
  have hreflect (θ : ℝ) : f (Real.pi - θ) = f θ := by
    dsimp [f]; rw [Real.cos_pi_sub, Real.sin_pi_sub]; simp only [abs_neg, neg_sq]
  have hint (x y : ℝ) : IntervalIntegrable f volume x y :=
    hfcont.continuousOn.intervalIntegrable
  have hshift : (∫ θ in -Real.pi..0, f θ) = ∫ θ in 0..Real.pi, f θ := by
    calc
      _ = ∫ θ in -Real.pi..0, f (θ + Real.pi) := by
        apply intervalIntegral.integral_congr; exact fun θ _ => (hperiod θ).symm
      _ = _ := by simpa [neg_add_cancel] using
        (intervalIntegral.integral_comp_add_right (f := f) (a := -Real.pi) (b := (0 : ℝ)) Real.pi)
  have hreflectInt : (∫ θ in Real.pi / 2..Real.pi, f θ) =
      ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
    calc
      _ = ∫ θ in (0 : ℝ)..(Real.pi / 2), f (Real.pi - θ) := by
        symm
        convert (intervalIntegral.integral_comp_sub_left (f := f) (a := (0 : ℝ))
          (b := Real.pi / 2) Real.pi) using 1 <;> ring
      _ = _ := by apply intervalIntegral.integral_congr; exact fun θ _ => hreflect θ
  have hhalf : (∫ θ in (0 : ℝ)..Real.pi, f θ) =
      2 * (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ) := by
    rw [(intervalIntegral.integral_add_adjacent_intervals
      (hint 0 (Real.pi / 2)) (hint (Real.pi / 2) Real.pi)).symm, hreflectInt]; ring
  have hfull : (∫ θ in -Real.pi..Real.pi, f θ) =
      4 * (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ) := by
    rw [(intervalIntegral.integral_add_adjacent_intervals
      (hint (-Real.pi) 0) (hint 0 Real.pi)).symm, hshift, hhalf]; ring
  have hrange : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < a + (b - a) * s ^ 2 := by
    intro s hs
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    have hs2le : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    have heq : a + (b - a) * s ^ 2 = a * (1 - s ^ 2) + b * s ^ 2 := by ring
    by_cases hone : s ^ 2 = 1
    · rw [heq, hone]
      simpa using hb
    · rw [heq]
      have hlt : s ^ 2 < 1 := lt_of_le_of_ne hs2le hone
      exact add_pos_of_pos_of_nonneg (mul_pos ha (by linarith))
        (mul_nonneg hb.le hs2)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := Real.pi / 2) (f := Real.sin) (f' := Real.cos) (g := g)
      Real.continuous_sin.continuousOn
      (by intro θ hθ; exact Real.hasDerivAt_sin θ)
      (by
        intro θ hθ
        have hθ' : 0 < θ ∧ θ < Real.pi / 2 := by
          simpa [min_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2),
            max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ
        exact Real.cos_nonneg_of_mem_Icc
          ⟨by nlinarith [Real.pi_pos, hθ'.1], by linarith [hθ'.2]⟩)
  have hquarterpoint (θ : ℝ) (hθ : θ ∈ Set.uIcc (0 : ℝ) (Real.pi / 2)) :
      f θ = (g ∘ Real.sin) θ * Real.cos θ := by
    have hθ' : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      simpa only [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ
    have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
      ⟨by nlinarith [Real.pi_pos, hθ'.1], by nlinarith [Real.pi_pos, hθ'.2]⟩
    have hq : a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2 = a + (b - a) * Real.sin θ ^ 2 :=
      by nlinarith [Real.sin_sq_add_cos_sq θ]
    dsimp [f, g]; rw [abs_of_nonneg hc, hq]; ring
  have hquarter : (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ) =
      ∫ s in (0 : ℝ)..1, g s := by
    calc
      _ = ∫ θ in (0 : ℝ)..(Real.pi / 2), (g ∘ Real.sin) θ * Real.cos θ := by
        apply intervalIntegral.integral_congr; exact fun θ hθ => hquarterpoint θ hθ
      _ = ∫ s in (0 : ℝ)..1, g s := by simpa using hsub
  have hscaleInt : (∫ s in (0 : ℝ)..1, g s) =
      (1 / a) * (∫ s in (0 : ℝ)..1, (1 + (b / a - 1) * s ^ 2)⁻¹) := by
    calc
      _ = ∫ s in (0 : ℝ)..1, (1 / a) *
          (1 + (b / a - 1) * s ^ 2)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
          simpa only [Set.uIcc_of_le zero_le_one] using hs
        have hfac : a + (b - a) * s ^ 2 = a * (1 + (b / a - 1) * s ^ 2) := by
          field_simp [ha.ne'] <;> ring
        have hinner : 1 + (b / a - 1) * s ^ 2 ≠ 0 := by
          intro hz
          have hz' : a + (b - a) * s ^ 2 = 0 := by rw [hfac, hz]; simp
          exact (ne_of_gt (hrange s hs')) hz'
        dsimp [g]
        rw [hfac]
        field_simp [ha.ne', hinner]
        <;> ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [hfull, hquarter, hscaleInt]
  ring

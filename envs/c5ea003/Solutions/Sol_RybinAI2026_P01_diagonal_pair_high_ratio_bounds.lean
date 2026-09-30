-- Prove2me | solution 1 for RybinAI2026.P01.diagonal_pair_high_ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T02:52:24.898773+00:00
-- url     : https://prove2.me/submissions/b3b2742b-2ec0-4b7b-aa81-fede8e8f8b5a

import Mathlib
import Theorems.Thm_RybinAI2026_P01_ratio_bound_of_slope_weight_antitone

theorem solution (G : ℝ → ℝ)
    (hGpos : ∀ t, 0 < t → 0 < G t)
    (hanti : AntitoneOn (fun t : ℝ => G t * (1 + (Real.sqrt t)⁻¹)) (Set.Ioi 0))
    (x y T : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (hT : 0 < T) (hxy : 1 < x + y) :
    let α : ℝ := x / (1 - y)
    let β : ℝ := y / (1 - x)
    let A : ℝ := Real.sqrt (x * (1 - y))
    let B : ℝ := Real.sqrt (y * (1 - x))
    let z : ℝ := Real.sqrt T
    A * (G T / G (T / α)) ≤ (x + A * z) / (1 + z) ∧
      B * (G (1 / T) / G (1 / (β * T))) ≤ (B + y * z) / (1 + z) := by
  dsimp
  let α := x / (1 - y)
  let β := y / (1 - x)
  let A := Real.sqrt (x * (1 - y))
  let B := Real.sqrt (y * (1 - x))
  let z := Real.sqrt T
  have h1y : 0 < 1 - y := sub_pos.mpr hy1
  have h1x : 0 < 1 - x := sub_pos.mpr hx1
  have hαpos : 0 < α := div_pos hx0 h1y
  have hβpos : 0 < β := div_pos hy0 h1x
  have hαgt : 1 < α := by
    dsimp [α]
    rw [lt_div_iff₀ h1y]
    nlinarith
  have hβgt : 1 < β := by
    dsimp [β]
    rw [lt_div_iff₀ h1x]
    nlinarith
  have hApos : 0 < A := Real.sqrt_pos.2 (mul_pos hx0 h1y)
  have hBpos : 0 < B := Real.sqrt_pos.2 (mul_pos hy0 h1x)
  have hzpos : 0 < z := Real.sqrt_pos.2 hT
  have ha1 : 0 < T / α := div_pos hT hαpos
  have hab1 : T / α ≤ T := (div_le_iff₀ hαpos).2 (by
    have hm := mul_pos hT (sub_pos.mpr (show 0 < α - 1 by linarith))
    nlinarith)
  have hr1 := RybinAI2026.P01.ratio_bound_of_slope_weight_antitone
    G hGpos hanti (T / α) T ha1 hT hab1
  have hr1' : G T / G (T / α) ≤ (Real.sqrt α + z) / (1 + z) := by
    calc
      _ ≤ (1 + (Real.sqrt (T / α))⁻¹) / (1 + (Real.sqrt T)⁻¹) := hr1
      _ = (Real.sqrt α + z) / (1 + z) := by
        rw [Real.sqrt_div hT.le]
        dsimp [z]
        field_simp [ne_of_gt (Real.sqrt_pos.2 hT),
          ne_of_gt (Real.sqrt_pos.2 hαpos),
          ne_of_gt (by positivity : 0 < 1 + (Real.sqrt T)⁻¹),
          ne_of_gt (by positivity : 0 < 1 + Real.sqrt T)]
        <;> ring
  have hAroot : A * Real.sqrt α = x := by
    dsimp [A, α]
    rw [Real.sqrt_mul hx0.le, Real.sqrt_div hx0.le]
    have hyroot : Real.sqrt (1 - y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h1y)
    calc
      _ = (Real.sqrt x) ^ 2 := by
        field_simp [hyroot]
      _ = x := Real.sq_sqrt hx0.le
  have hdenz : 0 < 1 + z := by linarith
  have hfirst : A * (G T / G (T / α)) ≤ (x + A * z) / (1 + z) := by
    calc
      _ ≤ A * ((Real.sqrt α + z) / (1 + z)) :=
        mul_le_mul_of_nonneg_left hr1' (le_of_lt hApos)
      _ = _ := by
        calc
          _ = (A * Real.sqrt α + A * z) / (1 + z) := by ring
          _ = (x + A * z) / (1 + z) := by rw [hAroot]
  have hβT : T ≤ β * T := by
    have hm := mul_pos hT (sub_pos.mpr (show 0 < β - 1 by linarith))
    nlinarith
  have hab2 : 1 / (β * T) ≤ 1 / T := one_div_le_one_div_of_le hT hβT
  have ha2 : 0 < 1 / (β * T) := one_div_pos.mpr (mul_pos hβpos hT)
  have hb2 : 0 < 1 / T := one_div_pos.mpr hT
  have hr2 := RybinAI2026.P01.ratio_bound_of_slope_weight_antitone
    G hGpos hanti (1 / (β * T)) (1 / T) ha2 hb2 hab2
  have hrootβ : (Real.sqrt (1 / (β * T)))⁻¹ = Real.sqrt β * z := by
    rw [show 1 / (β * T) = (β * T)⁻¹ by ring]
    simp only [Real.sqrt_inv, inv_inv]
    rw [Real.sqrt_mul hβpos.le]
  have hrootT : (Real.sqrt (1 / T))⁻¹ = z := by
    rw [show 1 / T = T⁻¹ by ring]
    simp only [Real.sqrt_inv, inv_inv]
    rfl
  have hr2' : G (1 / T) / G (1 / (β * T)) ≤
      (1 + Real.sqrt β * z) / (1 + z) := by
    calc
      _ ≤ (1 + (Real.sqrt (1 / (β * T)))⁻¹) /
          (1 + (Real.sqrt (1 / T))⁻¹) := hr2
      _ = _ := by rw [hrootβ, hrootT]
  have hBroot : B * Real.sqrt β = y := by
    dsimp [B, β]
    rw [Real.sqrt_mul hy0.le, Real.sqrt_div hy0.le]
    have hxroot : Real.sqrt (1 - x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h1x)
    calc
      _ = (Real.sqrt y) ^ 2 := by
        field_simp [hxroot]
      _ = y := Real.sq_sqrt hy0.le
  have hsecond : B * (G (1 / T) / G (1 / (β * T))) ≤
      (B + y * z) / (1 + z) := by
    calc
      _ ≤ B * ((1 + Real.sqrt β * z) / (1 + z)) :=
        mul_le_mul_of_nonneg_left hr2' (le_of_lt hBpos)
      _ = _ := by
        calc
          _ = (B + B * Real.sqrt β * z) / (1 + z) := by ring
          _ = (B + y * z) / (1 + z) := by rw [hBroot]
  exact ⟨hfirst, hsecond⟩

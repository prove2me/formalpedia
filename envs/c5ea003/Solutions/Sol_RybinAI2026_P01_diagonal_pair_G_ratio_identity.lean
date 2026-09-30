-- Prove2me | solution 1 for RybinAI2026.P01.diagonal_pair_G_ratio_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T02:52:46.538121+00:00
-- url     : https://prove2.me/submissions/39302bd3-8046-4079-8c72-cc8697049333

import Mathlib
import Theorems.Thm_RybinAI2026_P01_psi_integral_pos

theorem solution (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
    let G : ℝ → ℝ := fun t => Real.sqrt t * ψ t
    let x : ℝ := a / (a + c)
    let y : ℝ := d / (b + d)
    let T : ℝ := (b + d) / (a + c)
    let α : ℝ := x / (1 - y)
    let β : ℝ := y / (1 - x)
    let A : ℝ := Real.sqrt (x * (1 - y))
    let B : ℝ := Real.sqrt (y * (1 - x))
    x * (ψ T / ψ (b / a)) = A * (G T / G (T / α)) ∧
      y * (ψ (1 / T) / ψ (c / d)) =
        B * (G (1 / T) / G (1 / (β * T))) := by
  let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
  let G : ℝ → ℝ := fun t => Real.sqrt t * ψ t
  let x : ℝ := a / (a + c)
  let y : ℝ := d / (b + d)
  let T : ℝ := (b + d) / (a + c)
  let α : ℝ := x / (1 - y)
  let β : ℝ := y / (1 - x)
  let A : ℝ := Real.sqrt (x * (1 - y))
  let B : ℝ := Real.sqrt (y * (1 - x))
  change x * (ψ T / ψ (b / a)) = A * (G T / G (T / α)) ∧
    y * (ψ (1 / T) / ψ (c / d)) = B * (G (1 / T) / G (1 / (β * T)))
  have hac : 0 < a + c := add_pos ha hc
  have hbd : 0 < b + d := add_pos hb hd
  have hx : 0 < x := div_pos ha hac
  have hy : 0 < y := div_pos hd hbd
  have hx1 : x < 1 := by
    dsimp [x]
    exact (div_lt_iff₀ hac).2 (by linarith)
  have hy1 : y < 1 := by
    dsimp [y]
    exact (div_lt_iff₀ hbd).2 (by linarith)
  have h1x : 0 < 1 - x := sub_pos.mpr hx1
  have h1y : 0 < 1 - y := sub_pos.mpr hy1
  have hT : 0 < T := div_pos (add_pos hb hd) hac
  have hα : 0 < α := div_pos hx h1y
  have hβ : 0 < β := div_pos hy h1x
  have hTa : 0 < T / α := div_pos hT hα
  have hβT : 0 < β * T := mul_pos hβ hT
  have h1T : 0 < 1 / T := one_div_pos.mpr hT
  have hβT' : 0 < 1 / (β * T) := one_div_pos.mpr hβT
  have hTaId : T / α = b / a := by
    dsimp [T, α, x, y]
    field_simp [hac.ne', hbd.ne', ha.ne', h1y.ne'] <;> ring
  have hβTId : 1 / (β * T) = c / d := by
    dsimp [β, T, x, y]
    field_simp [h1x.ne', hbd.ne', hac.ne', hc.ne'] <;> ring
  have hq1 : T / (T / α) = α := by
    field_simp [hT.ne', hα.ne'] <;> ring
  have hroot1 : Real.sqrt T / Real.sqrt (T / α) = Real.sqrt α := by
    rw [← Real.sqrt_div hT.le, hq1]
  have hq2 : (1 / T) / (1 / (β * T)) = β := by
    field_simp [hT.ne', hβT.ne'] <;> ring
  have hroot2 : Real.sqrt (1 / T) / Real.sqrt (1 / (β * T)) = Real.sqrt β := by
    rw [← Real.sqrt_div (div_nonneg (by norm_num) hT.le), hq2]
  have hψT : 0 < ψ T := by
    dsimp [ψ]
    exact RybinAI2026.P01.psi_integral_pos T hT
  have hψba : 0 < ψ (b / a) := by
    dsimp [ψ]
    exact RybinAI2026.P01.psi_integral_pos (b / a) (div_pos hb ha)
  have hψ1T : 0 < ψ (1 / T) := by
    dsimp [ψ]
    exact RybinAI2026.P01.psi_integral_pos (1 / T) h1T
  have hψcd : 0 < ψ (c / d) := by
    dsimp [ψ]
    exact RybinAI2026.P01.psi_integral_pos (c / d) (div_pos hc hd)
  have hGr1 : G T / G (T / α) =
      Real.sqrt α * (ψ T / ψ (b / a)) := by
    dsimp [G]
    calc
      _ = (Real.sqrt T / Real.sqrt (T / α)) *
          (ψ T / ψ (T / α)) := by
        field_simp [hTaId, ne_of_gt hψba, ne_of_gt (Real.sqrt_pos.2 hT),
          ne_of_gt (Real.sqrt_pos.2 hTa)] <;> ring
      _ = Real.sqrt α * (ψ T / ψ (T / α)) := by rw [hroot1]
      _ = Real.sqrt α * (ψ T / ψ (b / a)) := by rw [hTaId]
  have hGr2 : G (1 / T) / G (1 / (β * T)) =
      Real.sqrt β * (ψ (1 / T) / ψ (c / d)) := by
    dsimp [G]
    calc
      _ = (Real.sqrt (1 / T) / Real.sqrt (1 / (β * T))) *
          (ψ (1 / T) / ψ (1 / (β * T))) := by
        field_simp [hβTId, ne_of_gt hψcd, ne_of_gt (Real.sqrt_pos.2 h1T),
          ne_of_gt (Real.sqrt_pos.2 hβT')] <;> ring
      _ = Real.sqrt β * (ψ (1 / T) / ψ (1 / (β * T))) := by rw [hroot2]
      _ = Real.sqrt β * (ψ (1 / T) / ψ (c / d)) := by rw [hβTId]
  have hAroot : A * Real.sqrt α = x := by
    dsimp [A, α]
    rw [Real.sqrt_mul hx.le, Real.sqrt_div hx.le]
    have hroot : Real.sqrt (1 - y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h1y)
    calc
      _ = (Real.sqrt x) ^ 2 := by field_simp [hroot] <;> ring
      _ = x := Real.sq_sqrt hx.le
  have hBroot : B * Real.sqrt β = y := by
    dsimp [B, β]
    rw [Real.sqrt_mul hy.le, Real.sqrt_div hy.le]
    have hroot : Real.sqrt (1 - x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h1x)
    calc
      _ = (Real.sqrt y) ^ 2 := by field_simp [hroot] <;> ring
      _ = y := Real.sq_sqrt hy.le
  constructor
  · calc
      x * (ψ T / ψ (b / a)) = A * (Real.sqrt α * (ψ T / ψ (b / a))) := by
        rw [← hAroot]
        ring
      _ = A * (G T / G (T / α)) := by rw [← hGr1]
  · calc
      y * (ψ (1 / T) / ψ (c / d)) =
          B * (Real.sqrt β * (ψ (1 / T) / ψ (c / d))) := by
        rw [← hBroot]
        ring
      _ = B * (G (1 / T) / G (1 / (β * T))) := by rw [← hGr2]

-- Prove2me | solution 1 for lean_workbook_plus_57779
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:20:13.98949+00:00
-- url     : https://prove2.me/submissions/1d4fe563-618d-412f-a97f-efc2753137c5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a - b) / (b + c) + (b - c) / (c + a) + (c - a) / (a + b) < 1 / 2   := by
  obtain ⟨ha, hb, hc⟩ := hx
  let u := (a + b - c) / 2
  let v := (b + c - a) / 2
  let w := (c + a - b) / 2
  have hu : 0 < u := by dsimp [u]; linarith
  have hv : 0 < v := by dsimp [v]; linarith
  have hw : 0 < w := by dsimp [w]; linarith
  have hab0 : a + b ≠ 0 := ne_of_gt (by positivity)
  have hbc0 : b + c ≠ 0 := ne_of_gt (by positivity)
  have hca0 : c + a ≠ 0 := ne_of_gt (by positivity)
  have heq : (1 / 2 - ((a - b) / (b + c) + (b - c) / (c + a) + (c - a) / (a + b))) * (2 * ((a + b) * (b + c) * (c + a))) =
      5 * u ^ 2 * v + 7 * u ^ 2 * w + 7 * u * v ^ 2 + 28 * u * v * w + 5 * u * w ^ 2 + 5 * v ^ 2 * w + 7 * v * w ^ 2 := by
    dsimp [u, v, w]
    field_simp [hab0, hbc0, hca0]
    <;> ring
  have hpos : 0 < 5 * u ^ 2 * v + 7 * u ^ 2 * w + 7 * u * v ^ 2 + 28 * u * v * w + 5 * u * w ^ 2 + 5 * v ^ 2 * w + 7 * v * w ^ 2 := by positivity
  have hden : 0 < 2 * ((a + b) * (b + c) * (c + a)) := by positivity
  have hd : 0 < 1 / 2 - ((a - b) / (b + c) + (b - c) / (c + a) + (c - a) / (a + b)) := (mul_pos_iff_of_pos_right hden).mp (by rw [heq]; exact hpos)
  linarith

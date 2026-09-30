-- Prove2me | solution 1 for lean_workbook_plus_27320
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:20:59.163849+00:00
-- url     : https://prove2.me/submissions/76156918-b854-434c-821b-eeb338d03c02

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) (h : x * y * z = (1 - x) * (1 - y) * (1 - z)) : (1 - x) * y ≥ 1 / 4 ∨ (1 - y) * z ≥ 1 / 4 ∨ (1 - z) * x ≥ 1 / 4 := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hz0, hz1⟩ := hz
  have h1 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have h2 : y * (1 - y) ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1 / 2)]
  have h3 : z * (1 - z) ≤ 1 / 4 := by nlinarith [sq_nonneg (z - 1 / 2)]
  have ha : 0 ≤ x * (1 - x) := by nlinarith
  have hb : 0 ≤ y * (1 - y) := by nlinarith
  have hc : 0 ≤ z * (1 - z) := by nlinarith
  have hsq : (x * y * z) ^ 2 ≤ 1 / 64 := by
    have e : (x * y * z) ^ 2 = (x * (1 - x)) * (y * (1 - y)) * (z * (1 - z)) := by
      calc (x * y * z) ^ 2 = (x * y * z) * ((1 - x) * (1 - y) * (1 - z)) := by rw [sq, ← h]
        _ = (x * (1 - x)) * (y * (1 - y)) * (z * (1 - z)) := by ring
    rw [e]
    calc (x * (1 - x)) * (y * (1 - y)) * (z * (1 - z)) ≤ (1 / 4) * (1 / 4) * (1 / 4) := by gcongr
      _ = 1 / 64 := by norm_num
  have hpos : 0 < x * y * z := mul_pos (mul_pos hx0 hy0) hz0
  have hp : x * y * z ≤ 1 / 8 := by nlinarith [hsq, hpos]
  have hsum : (1 - x) * y + (1 - y) * z + (1 - z) * x = 1 - 2 * (x * y * z) := by
    linear_combination h
  by_contra hcon
  push_neg at hcon
  obtain ⟨c1, c2, c3⟩ := hcon
  linarith

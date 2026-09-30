-- Prove2me | solution 1 for lean_workbook_plus_30715
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:27.24679+00:00
-- url     : https://prove2.me/submissions/a0fdce07-bc6b-438f-b889-97eb219de7a1

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z a b c : ℝ) (hx: x ≥ y ∧ y ≥ z ∧ z ≥ 0) (hab : a ≥ b ∧ b ≥ c ∧ c ≥ 0) : x * (a - b) * (a - c) + y * (b - a) * (b - c) + z * (c - b) * (c - a) ≥ 0 := by
  obtain ⟨hxy, hyz, hz⟩ := hx
  obtain ⟨hab, hbc, hc⟩ := hab
  have hy : 0 ≤ y := le_trans hz hyz
  have h1 : 0 ≤ (x - y) * ((a - b) * (a - c)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have h2 : 0 ≤ y * ((a - b) * (a - b)) :=
    mul_nonneg hy (mul_nonneg (by linarith) (by linarith))
  have h3 : 0 ≤ z * ((b - c) * (a - c)) :=
    mul_nonneg hz (mul_nonneg (by linarith) (by linarith))
  nlinarith [h1, h2, h3]

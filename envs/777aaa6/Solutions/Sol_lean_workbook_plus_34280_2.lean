-- Prove2me | solution 2 for lean_workbook_plus_34280
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:09.303596+00:00
-- url     : https://prove2.me/submissions/76ffc044-f329-4b6e-a281-35f49c802e64

import Mathlib.Analysis.Complex.Basic

theorem solution  (x b k : ℤ)
  (h₀ : x - 1 = 2 * k)
  (h₁ : x + 1 = 2 * k + 2)
  (h₂ : 8 * b = 4 * k * (k + 1)) :
  b = k * (k + 1) / 2 := by
  have h : k * (k + 1) = 2 * b := by linarith
  rw [h]
  omega

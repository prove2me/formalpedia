-- Prove2me | solution 1 for lean_workbook_plus_32227
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:39:47.928027+00:00
-- url     : https://prove2.me/submissions/07a76f6d-daeb-49b9-862c-299ad1fc448a

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (h : n > 2) : n^3 - n + 1 > n^2 + n + 1 := by
  have hle : n ≤ n ^ 3 := Nat.le_self_pow (by norm_num) n
  zify [hle] at h ⊢
  nlinarith

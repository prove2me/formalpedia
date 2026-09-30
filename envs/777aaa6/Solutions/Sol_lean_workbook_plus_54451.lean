-- Prove2me | solution 1 for lean_workbook_plus_54451
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:21:54.41611+00:00
-- url     : https://prove2.me/submissions/feaceb44-5d1c-4cce-98d1-c5ed2a4815af

import Mathlib.Analysis.Complex.Basic

theorem solution (t1 t2 : ℕ) (h : t1 + t2 ≥ t1 * t2 + 1) :
  (t2 + 1)^2 * (t1 + 1)^2 ≥ 4 * (t1 * t2 + 1)^2 := by
  have h1 : 2 * (t1 * t2 + 1) ≤ (t2 + 1) * (t1 + 1) := by nlinarith
  calc 4 * (t1 * t2 + 1)^2 = (2 * (t1 * t2 + 1))^2 := by ring
    _ ≤ ((t2 + 1) * (t1 + 1))^2 := Nat.pow_le_pow_left h1 2
    _ = (t2 + 1)^2 * (t1 + 1)^2 := by ring

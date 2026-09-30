-- Prove2me | solution 1 for lean_workbook_plus_64530
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:44:51.035384+00:00
-- url     : https://prove2.me/submissions/5d049c6f-f689-4463-82fc-ace9b670fa1d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

theorem solution (a : ℕ → ℝ) (n : ℕ) :
    a (n + 2) / 3 = ((n + 3) * a (n + 1)) / (3 * (n + 1)) ↔
      a (n + 2) / ((n + 2) * (n + 3)) = a (n + 1) / ((n + 1) * (n + 2)) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (n : ℝ) + 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) + 2 ≠ 0 := by linarith
  have h3 : (n : ℝ) + 3 ≠ 0 := by linarith
  field_simp [h1, h2, h3]

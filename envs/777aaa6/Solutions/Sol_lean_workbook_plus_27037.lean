-- Prove2me | solution 1 for lean_workbook_plus_27037
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:00:52.440069+00:00
-- url     : https://prove2.me/submissions/2f0fb80e-24e5-496a-b7f4-f872cc64e72b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (A B C D : ℝ) :
    (8 = A + B + C + D ∧ 16 = A + 2 * B + 4 * C + 8 * D ∧
      0 = A + 3 * B + 9 * C + 27 * D ∧
      -64 = A + 4 * B + 16 * C + 64 * D) ↔
    A = 0 ∧ B = 0 ∧ C = 12 ∧ D = -4 := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num

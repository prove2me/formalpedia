-- Prove2me | solution 1 for lean_workbook_plus_41796
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:42:25.253972+00:00
-- url     : https://prove2.me/submissions/a3704cca-b4fd-4932-aac1-20c36e666f45

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (f : ℝ → ℝ)
    (hf : ∀ x, x ≠ 0 ∧ x ≠ 1 → f x + f (1 / (1 - x)) = x) :
    f 5 = 121 / 40 := by
  have h1 := hf 5 (by norm_num)
  have h2 := hf (-1 / 4) (by norm_num)
  have h3 := hf (4 / 5) (by norm_num)
  norm_num at h1 h2 h3
  linarith! only [h1, h2, h3]

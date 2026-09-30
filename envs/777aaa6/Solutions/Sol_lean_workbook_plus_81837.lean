-- Prove2me | solution 1 for lean_workbook_plus_81837
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:38:55.985256+00:00
-- url     : https://prove2.me/submissions/ea0bbb00-5253-4465-8f9d-7919444af3da

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution : ∃ x y z : ℤ, x^2+y^2+z^2 = 2 := by
  exact ⟨1, 1, 0, by norm_num⟩

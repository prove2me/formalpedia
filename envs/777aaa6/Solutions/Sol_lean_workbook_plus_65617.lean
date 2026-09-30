-- Prove2me | solution 1 for lean_workbook_plus_65617
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:44:38.111281+00:00
-- url     : https://prove2.me/submissions/54e6b2c9-b03d-4455-932f-707f65efaeda

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ (a b c : ℝ), a = 20806 → b = 408 → c^2 = a^2 + b^2 → c = 20874) := by
  intro h
  have := h 20806 408 20810 rfl rfl (by norm_num)
  norm_num at this

-- Prove2me | solution 1 for lean_workbook_plus_48944
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:44.611522+00:00
-- url     : https://prove2.me/submissions/45eccd5a-3c41-4148-bfc1-365eebfe2546

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, (a^8061 / (a^2 + 1) + b^29 / (b^2 + 1) + c^121 / (c^2 + 1) + 4101 / 2) ≥ 2015 * a^2 + 7 * b^2 + 30 * c^2) := by
  intro h
  have h1 := h 0 (-2) 0
  have e0 : (0:ℝ)^8061 = 0 := by simp
  have e0' : (0:ℝ)^121 = 0 := by simp
  have e00 : (0:ℝ)^2 = 0 := by simp
  have e2 : (-2:ℝ)^2 = 4 := by norm_num
  have e29 : (-2:ℝ)^29 = -536870912 := by norm_num
  rw [e0, e0', e00, e2, e29] at h1
  linarith

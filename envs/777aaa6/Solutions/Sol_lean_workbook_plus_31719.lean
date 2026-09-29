-- Prove2me | solution 1 for lean_workbook_plus_31719
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:55.164053+00:00
-- url     : https://prove2.me/submissions/f69ebcaa-1b73-4aec-ae04-5dfb78eee9c4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (gV realweight : ℝ) (h₁ : gV = (realweight - 15) / 1.1) (h₂ : realweight - 1.2 * gV = 10) : realweight = 70 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg gV, sq_nonneg realweight, sq_nonneg (gV - realweight)]

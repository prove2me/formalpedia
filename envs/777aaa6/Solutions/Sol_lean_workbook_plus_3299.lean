-- Prove2me | solution 1 for lean_workbook_plus_3299
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:44.979683+00:00
-- url     : https://prove2.me/submissions/f1ca3cc6-378c-4454-b243-8496c88eeb76

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c k : ℝ) : (k = (c - a) / (b - a) ∧ k = -((c - a) / (a - b))) → 1 / k = -(a - b) / (c - a) := by
  (intros; simp_all)

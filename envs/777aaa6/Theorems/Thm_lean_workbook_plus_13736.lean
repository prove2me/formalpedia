-- Prove2me | Theorems.Thm_lean_workbook_plus_13736
-- name    : lean_workbook_plus_13736
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/baefb83f-3b61-4716-ba7d-481d05666d89
-- statement:
--   Prove that $|\cos{x}|+|\cos{2x}|+|\cos{3x}|+|\cos{4x}|{\ge} 1+\frac{ \sqrt{3} }{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13736 : ∀ x : ℝ, 1 + Real.sqrt 3 / 2 ≤ abs (cos x) + abs (cos 2 * x) + abs (cos 3 * x) + abs (cos 4 * x)   :=  by sorry

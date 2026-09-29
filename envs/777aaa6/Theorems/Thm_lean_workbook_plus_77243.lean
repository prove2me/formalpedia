-- Prove2me | Theorems.Thm_lean_workbook_plus_77243
-- name    : lean_workbook_plus_77243
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/3dd0de7f-cd92-4d4d-9e4e-618d43060437
-- statement:
--   Prove that \((a+b)(4+ab) \ge 8ab\) for \(a,b \ge 0\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77243 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) * (4 + a * b) ≥ 8 * a * b   :=  by sorry

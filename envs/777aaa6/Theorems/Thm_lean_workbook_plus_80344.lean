-- Prove2me | Theorems.Thm_lean_workbook_plus_80344
-- name    : lean_workbook_plus_80344
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/d8cbfa17-af1a-4c22-a0a7-0f5de8ef5e76
-- statement:
--   Prove that $2\\sin(a) \\sin(b) = \\cos(a - b) - \\cos(a + b)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80344 (a b : ℝ) : 2 * sin a * sin b = cos (a - b) - cos (a + b)   :=  by sorry

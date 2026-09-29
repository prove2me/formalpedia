-- Prove2me | Theorems.Thm_lean_workbook_plus_1512
-- name    : lean_workbook_plus_1512
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/bf05c1c2-ddfb-47b7-a46c-36b4020f149d
-- statement:
--   Prove that \(ab+bc+ca\le 3\) when \(a+b+c=3\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1512 (a b c : ℝ) (hab : a + b + c = 3) : a * b + b * c + c * a ≤ 3   :=  by sorry

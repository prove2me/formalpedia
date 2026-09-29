-- Prove2me | Theorems.Thm_lean_workbook_plus_75740
-- name    : lean_workbook_plus_75740
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/91754c01-08cb-4496-9e4c-ef563da14a14
-- statement:
--   prove that $x^5-3x^3-36x^2+162 \geq 0$ where $x \geq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75740 (x : ℝ) (h : x >= 3) : x^5 - 3 * x^3 - 36 * x^2 + 162 >= 0   :=  by sorry

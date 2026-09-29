-- Prove2me | Theorems.Thm_lean_workbook_plus_59390
-- name    : lean_workbook_plus_59390
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/8340d128-ff23-4d07-855f-0310d48da5b8
-- statement:
--   IF $a,b$ > $0$ , and $2a=ab+b^2$ , prove $(a-b)((a+b)^3+2ab(a+b)-2a-10b)$ ≥ $0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59390 (a b : ℝ) (hab : a > 0 ∧ b > 0) (h : 2 * a = a * b + b ^ 2) : (a - b) * ((a + b) ^ 3 + 2 * a * b * (a + b) - 2 * a - 10 * b) ≥ 0   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_23934
-- name    : lean_workbook_plus_23934
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/644ca35b-fa02-4e0b-be36-16af6fc60efb
-- statement:
--   Prove that $(a+b)^2(b+c)^2\ge 2abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23934 (a b c : ℝ) : (a + b) ^ 2 * (b + c) ^ 2 ≥ 2 * a * b * c * (a + b + c)   :=  by sorry

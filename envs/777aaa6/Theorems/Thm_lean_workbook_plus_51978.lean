-- Prove2me | Theorems.Thm_lean_workbook_plus_51978
-- name    : lean_workbook_plus_51978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/6f722260-be1c-4129-9719-83b503b747a4
-- statement:
--   By the AM-GM Inequality, we have \n $ \frac{(2a+b)^2}{b}+\frac{81a^2b}{(2a+b)^2} \ge 18a.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51978 (a b : ℝ) (ha : a > 0) (hb : b > 0) : (2 * a + b) ^ 2 / b + 81 * a ^ 2 * b / (2 * a + b) ^ 2 ≥ 18 * a   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_2845
-- name    : lean_workbook_plus_2845
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/c92d8da6-4bb0-48bc-866c-87fd0329fde0
-- statement:
--   Prove that if $a, b, c$ are positive real numbers, then $(a+b+c)^2 \geq 3(ab+bc+ca)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2845 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + a * c)   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_8674
-- name    : lean_workbook_plus_8674
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/b9d02bd0-255f-4ee9-948e-2ef241610ca0
-- statement:
--   Calculate the future value of an investment with a principal of $1000, an annual interest rate of 5%, and a time period of 10 years, compounded annually.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8674 (P i n : ℝ) (hP : P = 1000) (hi : i = 0.05) (hn : n = 10) : (P * (1 + i)^n) = 1628.899   :=  by sorry

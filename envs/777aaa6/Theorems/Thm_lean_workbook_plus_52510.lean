-- Prove2me | Theorems.Thm_lean_workbook_plus_52510
-- name    : lean_workbook_plus_52510
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/ca77fc0f-f1b6-44df-9e4e-c39742830c10
-- statement:
--   It is $\frac{(a-b)^2(b-c)^2(c-a)^2}{(a+b)^2(b+c)^2(c+a)^2}\ge0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52510 (a b c : ℝ) : (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 / (a + b) ^ 2 / (b + c) ^ 2 / (c + a) ^ 2 ≥ 0   :=  by sorry

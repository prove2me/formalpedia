-- Prove2me | Theorems.Thm_lean_workbook_plus_18197
-- name    : lean_workbook_plus_18197
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/9d06b9e1-d46f-452e-821c-0c4556d8a71d
-- statement:
--   Suppose $a,b,c\ge 0$ , prove that \n $\left( 13a-5b+c \right){{(a-b)}^{2}}+\left( 13b-5c+a \right){{(b-c)}^{2}}+\left( 13c-5a+b \right){{(c-a)}^{2}}$ $\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18197 (a b c : ℝ) (hab : a - b ≥ 0) (hbc : b - c ≥ 0) (hca : c - a ≥ 0) : (13 * a - 5 * b + c) * (a - b) ^ 2 + (13 * b - 5 * c + a) * (b - c) ^ 2 + (13 * c - 5 * a + b) * (c - a) ^ 2 ≥ 0   :=  by sorry

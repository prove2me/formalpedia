-- Prove2me | Theorems.Thm_lean_workbook_plus_79368
-- name    : lean_workbook_plus_79368
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/f8c7ce35-bbed-44d8-a2aa-4cc5e2c8fe6e
-- statement:
--   If $a,b,c$ are positive real numbers $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\ge 2(\frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{c+a})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79368 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / a + 1 / b + 1 / c) ≥ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))   :=  by sorry

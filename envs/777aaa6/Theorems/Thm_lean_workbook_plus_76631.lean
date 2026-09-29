-- Prove2me | Theorems.Thm_lean_workbook_plus_76631
-- name    : lean_workbook_plus_76631
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/c9494a6e-8759-4684-81be-5084813a8376
-- statement:
--   Given $a, b, c > 0$ , prove that $\frac{9}{a+b+c} \le 2(\frac{1}{a+b} + \frac{1}{b+c} + \frac{1}{c+a})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76631 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (9 / (a + b + c)) ≤ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))   :=  by sorry

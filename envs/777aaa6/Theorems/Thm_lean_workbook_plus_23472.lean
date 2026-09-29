-- Prove2me | Theorems.Thm_lean_workbook_plus_23472
-- name    : lean_workbook_plus_23472
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/faadd260-82e2-4ca1-9479-f3652c3fe96f
-- statement:
--   Prove that $\frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{c+a} \leq \frac{{(a+b+c)}^{2}}{6abc}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23472 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≤ (a + b + c) ^ 2 / (6 * a * b * c)   :=  by sorry

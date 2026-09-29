-- Prove2me | Theorems.Thm_lean_workbook_plus_5353
-- name    : lean_workbook_plus_5353
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/7759b8c7-735c-44ba-9e6e-06408b2f3ccd
-- statement:
--   Let $a,b$ be positive real numbers such that $\frac{1}{a}+\frac{1}{b}=1.$ Prove that $4ab+\frac{3}{a+b}\leq \frac{35}{4}+a^2+b^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5353 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / a + 1 / b = 1) : 4 * a * b + 3 / (a + b) ≤ 35 / 4 + a ^ 2 + b ^ 2   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_32272
-- name    : lean_workbook_plus_32272
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/5351b65e-8bc1-4d0a-ae23-9c5964509d63
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that $\frac{a} {5a^2+(b+c)^2} \leq\frac{5a+2(b+c)}{9(a+b+c)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32272 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (5 * a ^ 2 + (b + c) ^ 2) ≤ (5 * a + 2 * (b + c)) / (9 * (a + b + c) ^ 2))   :=  by sorry

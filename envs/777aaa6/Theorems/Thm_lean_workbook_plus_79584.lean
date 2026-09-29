-- Prove2me | Theorems.Thm_lean_workbook_plus_79584
-- name    : lean_workbook_plus_79584
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/d170c549-ce02-432d-8d65-b24e4a6b90eb
-- statement:
--   Let $a,b$ be positive real numbers such that $\frac{1}{a}+\frac{1}{b}=1.$ Prove that $6ab+\frac{1}{a+b}\leq \frac{65}{4}+a^2+b^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79584 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1/a + 1/b = 1) : 6*a*b + 1/(a + b) ≤ 65/4 + a^2 + b^2   :=  by sorry

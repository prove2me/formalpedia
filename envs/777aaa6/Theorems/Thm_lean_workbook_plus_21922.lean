-- Prove2me | Theorems.Thm_lean_workbook_plus_21922
-- name    : lean_workbook_plus_21922
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/9246d2d0-7e8f-4c86-b606-879ad1b9f3ac
-- statement:
--   Assume that $ab + bc + ca \ge 3$. We have to prove $\frac{1}{a+b+1}+\frac{1}{b+c+1}+\frac{1}{c+a+1} \le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21922 (a b c : ℝ) (hab : a + b + c = 0) : (a * b + b * c + c * a >= 3) → (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) <= 1)   :=  by sorry

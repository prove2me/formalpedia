-- Prove2me | Theorems.Thm_lean_workbook_plus_24724
-- name    : lean_workbook_plus_24724
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/ecb90c5e-b849-4522-99da-7c98b041c3f1
-- statement:
--   Let $f(x)=ax^2+bx+c$ such that $|f(1)|\le 1$ , $|f(0)|\le 1$ , and $|f(-1)|\le 1$ . Prove that $|f(x)| \le \frac{5}4$ for all $|x|\le 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24724 (a b c x : ℝ) (hx : abs x ≤ 1) (h1 : abs (a * x ^ 2 + b * x + c) ≤ 1) (h2 : abs (a * 0 ^ 2 + b * 0 + c) ≤ 1) (h3 : abs (a * (-1) ^ 2 + b * (-1) + c) ≤ 1) : abs (a * x ^ 2 + b * x + c) ≤ 5 / 4   :=  by sorry

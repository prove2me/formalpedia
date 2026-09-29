-- Prove2me | Theorems.Thm_lean_workbook_plus_76604
-- name    : lean_workbook_plus_76604
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/0354baf3-4d9f-4007-b88e-b085ea9a3a69
-- statement:
--   Prove that for any positive numbers $a, b, c$ such that $a > b > c > 2$, the expression $\max\{2a, \frac{3}{b}\} + \max\{3a, \frac{3}{2c}\} + \max\{\frac{3c}{2}, \frac{2}{a}\}$ is greater than 10.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76604 (a b c : ℝ) (h1 : a > b ∧ b > c ∧ c > 2) : (max (2 * a) (3 / b)) + (max (3 * a) (3 / (2 * c))) + (max ((3 * c) / 2) (2 / a)) > 10   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_25436
-- name    : lean_workbook_plus_25436
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/e7ae0f00-9db3-4378-ac5c-35633023cefc
-- statement:
--   Let $a, b, c$ be positive real numbers. Prove that \n $$\frac{1}{2a}+\frac{1}{2b}+\frac{1}{2c}\ge\frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{c+a}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25436 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c)) ≥ (1 / (a + b) + 1 / (b + c) + 1 / (c + a))   :=  by sorry

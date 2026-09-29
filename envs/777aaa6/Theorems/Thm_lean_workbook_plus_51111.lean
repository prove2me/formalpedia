-- Prove2me | Theorems.Thm_lean_workbook_plus_51111
-- name    : lean_workbook_plus_51111
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5f73091e-1260-44a7-a14a-33be367a13c8
-- statement:
--   Given $a, b > 0$ and $a + b + 1 = 3ab$, prove that $\frac{1}{a} + \frac{1}{b} \geq 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51111 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b + 1 = 3 * a * b) : 1 / a + 1 / b ≥ 2   :=  by sorry

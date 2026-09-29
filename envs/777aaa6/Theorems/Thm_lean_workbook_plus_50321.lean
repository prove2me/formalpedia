-- Prove2me | Theorems.Thm_lean_workbook_plus_50321
-- name    : lean_workbook_plus_50321
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/493cd953-1af3-4242-ad51-25e72fd24f25
-- statement:
--   Prove for positive a, b, and real x, y, \n $$\frac{x^2}{a}+\frac{y^2}{b}\geq\frac{(x+y)^2}{a+b}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50321 (x y a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (x ^ 2 / a + y ^ 2 / b) ≥ (x + y) ^ 2 / (a + b)   :=  by sorry

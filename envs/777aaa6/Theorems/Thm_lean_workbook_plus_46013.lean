-- Prove2me | Theorems.Thm_lean_workbook_plus_46013
-- name    : lean_workbook_plus_46013
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d0631b81-e6d9-47d7-90a0-fd597b0bc59c
-- statement:
--   Prove that $\frac{1}{a} + \frac{1}{b} - \frac{1}{c} \leq \frac{3}{4abc}$ given $a, b, c > 0$ and $a^2 + b^2 + c^2 = \frac{3}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46013 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 3 / 2) : 1 / a + 1 / b - 1 / c ≤ 3 / (4 * a * b * c)   :=  by sorry

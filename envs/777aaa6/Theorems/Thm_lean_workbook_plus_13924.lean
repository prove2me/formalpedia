-- Prove2me | Theorems.Thm_lean_workbook_plus_13924
-- name    : lean_workbook_plus_13924
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/e0718364-03ab-4809-8a22-01aabdcab939
-- statement:
--   Can we say that $1 + x + x^2 + x^3 + \ldots + x^n + \ldots = \frac{1}{1 - x}$ for $0 < x < 1$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13924 (x : ℝ) (hx : 0 < x ∧ x < 1) :
  ∑' i : ℕ, x ^ i = 1 / (1 - x)   :=  by sorry

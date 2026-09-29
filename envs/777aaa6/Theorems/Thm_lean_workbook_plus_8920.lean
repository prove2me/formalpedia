-- Prove2me | Theorems.Thm_lean_workbook_plus_8920
-- name    : lean_workbook_plus_8920
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/92ad3195-5e7a-41e2-96f1-a6bfb90cffbc
-- statement:
--   Find the value of $a$ in $\displaystyle \prod_{n=1}^{3}\frac{9^n}{3^n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8920 (a : ℝ) (h : a = ∏ n in Finset.Icc 1 3, (9^n / 3^n)) : a = 729   :=  by sorry

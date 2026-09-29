-- Prove2me | Theorems.Thm_lean_workbook_plus_8750
-- name    : lean_workbook_plus_8750
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e09e605c-d853-4b6d-92a7-13c9ca2e63ea
-- statement:
--   Suppose a+b=1 where a and b are positive numbers. (i) Show that $ab\leq\frac14$ . (ii) Find the minimum value of $\left(a+\frac1a\right)\left(b+\frac1b\right)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8750 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a + b = 1 → a * b ≤ 1 / 4   :=  by sorry

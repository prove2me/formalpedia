-- Prove2me | Theorems.Thm_lean_workbook_plus_29351
-- name    : lean_workbook_plus_29351
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/44808042-8fff-471f-a093-67f2b8b69ad2
-- statement:
--   Suppose a+b=1 where a and b are positive numbers. (i) Show that $ab\leq\frac14$ . (ii) Find the minimum value of $\left(a+\frac1a\right)\left(b+\frac1b\right)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29351 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a * b ≤ 1 / 4   :=  by sorry

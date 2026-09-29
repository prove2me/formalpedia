-- Prove2me | Theorems.Thm_lean_workbook_plus_59702
-- name    : lean_workbook_plus_59702
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/8b94b02e-5ce2-4952-90ef-f15bcd9fa21c
-- statement:
--   If $a,b,c >0$ and $a^2+b^2+c^2=1$ , prove that: $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+a+b+c \ge 4 \sqrt{3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59702 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : 1 / a + 1 / b + 1 / c + a + b + c ≥ 4 * Real.sqrt 3   :=  by sorry

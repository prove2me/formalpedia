-- Prove2me | Theorems.Thm_lean_workbook_plus_20239
-- name    : lean_workbook_plus_20239
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/f4fee22b-8be6-42d7-8961-f4f951988f33
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=1$. Prove that $\frac {1} {a} +\frac {1} {b} +\frac{1} {c} \geq \frac { 25} { 1+48abc}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20239 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / a + 1 / b + 1 / c ≥ 25 / (1 + 48 * a * b * c)   :=  by sorry

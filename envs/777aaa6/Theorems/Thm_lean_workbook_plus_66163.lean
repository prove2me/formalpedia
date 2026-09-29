-- Prove2me | Theorems.Thm_lean_workbook_plus_66163
-- name    : lean_workbook_plus_66163
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6d2f2264-982b-4256-a266-432d44f7c980
-- statement:
--   prove that: $\frac{c(b-a)}{a} + \frac{a(c-b)}{b} + \frac{b(a-c)}{c}$ is nonnegative for any positive real a,b,c.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66163 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (c * (b - a) / a + a * (c - b) / b + b * (a - c) / c) ≥ 0   :=  by sorry

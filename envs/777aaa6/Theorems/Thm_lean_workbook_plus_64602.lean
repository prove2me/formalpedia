-- Prove2me | Theorems.Thm_lean_workbook_plus_64602
-- name    : lean_workbook_plus_64602
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d3399e4e-7a8f-49b0-810b-314eaaa03f62
-- statement:
--   Given $a, b, c > 0$ and $a^2 + b^2 - ab = c^2$. Prove that $(a - c)(b - c) \leq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64602 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a^2 + b^2 - a * b = c^2) : (a - c) * (b - c) ≤ 0   :=  by sorry

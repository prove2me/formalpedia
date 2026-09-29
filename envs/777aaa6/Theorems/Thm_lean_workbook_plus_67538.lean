-- Prove2me | Theorems.Thm_lean_workbook_plus_67538
-- name    : lean_workbook_plus_67538
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/3e57d4f2-e187-439b-a504-e711085792f4
-- statement:
--   Prove that $\frac{a}{(a + 1)(b + 1)} +\frac{ b}{(b + 1)(c + 1)} + \frac{c}{(c + 1)(a + 1)} \ge \frac34$ where $a, b$ and $c$ are positive real numbers satisfying $abc = 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67538 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : (a / (a + 1) * b + 1) + (b / (b + 1) * c + 1) + (c / (c + 1) * a + 1) ≥ 3 / 4   :=  by sorry

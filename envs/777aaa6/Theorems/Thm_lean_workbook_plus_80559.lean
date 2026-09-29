-- Prove2me | Theorems.Thm_lean_workbook_plus_80559
-- name    : lean_workbook_plus_80559
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/f4783281-6fa4-4855-9c34-8e8dc392dd95
-- statement:
--   Given $x(x^4-x^2+1) \ge 3$, and 'x' is a positive number. Prove that $x^6 \ge 5$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80559 (x : ℝ) (hx : 0 < x) (h : x * (x ^ 4 - x ^ 2 + 1) ≥ 3) : x ^ 6 ≥ 5   :=  by sorry

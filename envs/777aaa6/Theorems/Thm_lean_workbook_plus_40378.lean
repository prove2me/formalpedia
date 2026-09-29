-- Prove2me | Theorems.Thm_lean_workbook_plus_40378
-- name    : lean_workbook_plus_40378
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/61f5f85a-ddb9-4c0a-b57e-792d0265ee7b
-- statement:
--   Find the roots of the equation $(s-t)^n = t$ for $s = 1$ and $n = 5$, i.e., solve $-t^5 + 5t^4 - 10t^3 + 10t^2 - 6t + 1 = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40378 (t : ℂ) : (1 - t)^5 = t ↔ -t^5 + 5 * t^4 - 10 * t^3 + 10 * t^2 - 6 * t + 1 = 0   :=  by sorry

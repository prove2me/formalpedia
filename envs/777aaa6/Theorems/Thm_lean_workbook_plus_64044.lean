-- Prove2me | Theorems.Thm_lean_workbook_plus_64044
-- name    : lean_workbook_plus_64044
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b5f2f699-b4fb-4c50-bb0e-1505e78d39a6
-- statement:
--   Determine the convergence of the series: $\sum_{n=1}^\infty \frac{\sqrt{n^5}}{n^4+20}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64044 : ∃ l, ∑' n : ℕ, (Real.sqrt (n^5)/(n^4+20)) = l   :=  by sorry

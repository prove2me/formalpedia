-- Prove2me | Theorems.Thm_lean_workbook_plus_79539
-- name    : lean_workbook_plus_79539
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/35fb1ece-62aa-4d68-833c-ad862403dee4
-- statement:
--   Factor the series and split into two separate series.\n\nWe have $\frac{n^3-1}{n^3+1}$ = $\frac{(n-1)(n^2+n+1)}{(n+1)(n^2-n+1)}$ = $\frac{n-1}{n+1} \frac{n^2+n+1}{n^2-n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79539 (n : ℕ) : ((n:ℝ)^3 - 1) / ((n:ℝ)^3 + 1) = (n - 1) / (n + 1) * ((n:ℝ)^2 + n + 1) / ((n:ℝ)^2 - n + 1)   :=  by sorry

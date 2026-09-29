-- Prove2me | Theorems.Thm_lean_workbook_plus_63931
-- name    : lean_workbook_plus_63931
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/3cdcb22a-a09d-4270-a39a-80c5548ffa54
-- statement:
--   The difference between $ n^2$ and $ 1$ is $ n^2-1$ , or $ (n+1)(n-1)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63931  (n : ℕ) :
  n^2 - 1 = (n + 1) * (n - 1)   :=  by sorry

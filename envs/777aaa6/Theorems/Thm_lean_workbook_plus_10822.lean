-- Prove2me | Theorems.Thm_lean_workbook_plus_10822
-- name    : lean_workbook_plus_10822
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3d58f7bd-eb1c-478d-b9ee-85b2ee750772
-- statement:
--   Find the sum of the series $1+2+\dots+999$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10822 : ∑ k in Finset.range 1000, k = 499500   :=  by sorry

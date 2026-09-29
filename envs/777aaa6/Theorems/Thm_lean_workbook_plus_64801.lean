-- Prove2me | Theorems.Thm_lean_workbook_plus_64801
-- name    : lean_workbook_plus_64801
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/7a950af3-9eae-44d8-aba6-e23d3dfe875a
-- statement:
--   Given two roots $r,s$ you should know that $4-r$ and $4-s$ will also be roots. The sum of these is 8.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64801 (r s : ℂ) (hr : r^2 - 8 * r + 12 = 0) (hs : s^2 - 8 * s + 12 = 0) : r + s + (4 - r) + (4 - s) = 8   :=  by sorry

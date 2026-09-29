-- Prove2me | Theorems.Thm_lean_workbook_plus_32190
-- name    : lean_workbook_plus_32190
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/242d7d3d-8943-4e4f-ac90-c184756edee1
-- statement:
--   Is the set of fractional parts of the harmonic sums dense in $ [0,1]$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32190 : Dense { (∑ k in Finset.range n, 1 / (k + 1)) % 1 | n }   :=  by sorry

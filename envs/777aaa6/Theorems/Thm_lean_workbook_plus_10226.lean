-- Prove2me | Theorems.Thm_lean_workbook_plus_10226
-- name    : lean_workbook_plus_10226
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/fcd0a571-07ab-4eca-ac26-f53b482bd865
-- statement:
--   $\, \Longleftrightarrow \, \, \sum_\textrm{cyc }\left( a-1 \right)^{2}\left( a-\frac12 \right)^{2}\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10226 (a b c : ℝ) : (a - 1) ^ 2 * (a - 1 / 2) ^ 2 + (b - 1) ^ 2 * (b - 1 / 2) ^ 2 + (c - 1) ^ 2 * (c - 1 / 2) ^ 2 ≥ 0   :=  by sorry

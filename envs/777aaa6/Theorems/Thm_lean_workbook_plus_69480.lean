-- Prove2me | Theorems.Thm_lean_workbook_plus_69480
-- name    : lean_workbook_plus_69480
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/b947a1ec-34f9-49d5-bcb0-24b7b8ebe4d3
-- statement:
--   For the first question, we have $\frac{n+2}{6n}=\frac15\implies n=\boxed{10}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69480 (n : ℝ) (hn : n ≠ 0) : ((n + 2) / (6 * n) : ℝ) = 1 / 5 ↔ n = 10   :=  by sorry

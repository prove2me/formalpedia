-- Prove2me | Theorems.Thm_lean_workbook_plus_61973
-- name    : lean_workbook_plus_61973
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/a6110fb7-fed9-488a-b07c-d3c2cc629a45
-- statement:
--   For positive integer $ k$ , let $ f_k(x) = \frac {1}{k}(\sin^k x + \cos^k x)$ Find the minimum possible value of $ f_4(x) - f_6(x)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61973 (x : ℝ) : 1 / 12 ≤ (1 / 4) * (sin x ^ 4 + cos x ^ 4) - (1 / 6) * (sin x ^ 6 + cos x ^ 6)   :=  by sorry

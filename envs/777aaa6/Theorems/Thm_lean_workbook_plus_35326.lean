-- Prove2me | Theorems.Thm_lean_workbook_plus_35326
-- name    : lean_workbook_plus_35326
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/fcad6615-02c6-410a-b789-357c925f5ea0
-- statement:
--   Rewrite and evaluate the series: $\sum_{n = 2}^{9}\frac {1}{n(n + 1)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35326 (n : ℕ) : ∑ n in Finset.Icc 2 9, (1/(n*(n+1))) = 4/5   :=  by sorry

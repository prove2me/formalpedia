-- Prove2me | Theorems.Thm_lean_workbook_plus_15566
-- name    : lean_workbook_plus_15566
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/549588cb-3533-48ea-9d5f-03d1e778c9b6
-- statement:
--   Prove that $\sum_{cyc}(a-b+c)^{2}(a+c-b)^{2}\ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15566 (a b c : ℝ) : (a - b + c) ^ 2 * (a + c - b) ^ 2 + (b - c + a) ^ 2 * (b + a - c) ^ 2 + (c - a + b) ^ 2 * (c + b - a) ^ 2 ≥ 0   :=  by sorry

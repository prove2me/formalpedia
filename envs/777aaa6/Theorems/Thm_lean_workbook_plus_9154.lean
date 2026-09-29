-- Prove2me | Theorems.Thm_lean_workbook_plus_9154
-- name    : lean_workbook_plus_9154
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ba52edce-8ba2-41cb-9dbb-123328cb2b72
-- statement:
--   Prove that $(1+\frac{1}{3})(1+\frac{1}{3^2})\cdots(1+\frac{1}{3^n})< 2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9154 : ∀ n : ℕ, (∏ k in Finset.range n, (1 + 1 / 3^k)) < 2   :=  by sorry

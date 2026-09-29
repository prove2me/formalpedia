-- Prove2me | Theorems.Thm_lean_workbook_plus_75948
-- name    : lean_workbook_plus_75948
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c1e6a1e3-c202-4d62-bc82-f03ba1c08f50
-- statement:
--   Prove that $(1-1/4)(1-1/9)(1-1/16) \cdots (1-1/(n^2)) > 1/2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75948 : ∀ n : ℕ, (∏ k in Finset.Icc 1 n, (1 - 1 / k ^ 2)) > 1 / 2   :=  by sorry

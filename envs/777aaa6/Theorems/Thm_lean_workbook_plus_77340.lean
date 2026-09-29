-- Prove2me | Theorems.Thm_lean_workbook_plus_77340
-- name    : lean_workbook_plus_77340
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/341ebc4e-6c40-4165-abfb-60b29746e6e2
-- statement:
--   $ \sum_{i=1}^{100} (5^i - 5^{i-1})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77340 : ∑ i in Finset.Icc 1 100, (5^i - 5^(i-1)) = 5^100 - 1   :=  by sorry

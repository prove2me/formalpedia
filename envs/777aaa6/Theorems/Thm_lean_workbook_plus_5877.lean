-- Prove2me | Theorems.Thm_lean_workbook_plus_5877
-- name    : lean_workbook_plus_5877
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/4903b072-f7db-4e44-8754-45c13d960970
-- statement:
--   $1+2+3+...+2019= \frac{2019 \cdot 2020}{2}=2019 \cdot 1010=2039190$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5877 :
  ∑ k in (Finset.range 2019), k = 2039190   :=  by sorry

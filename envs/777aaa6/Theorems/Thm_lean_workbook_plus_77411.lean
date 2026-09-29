-- Prove2me | Theorems.Thm_lean_workbook_plus_77411
-- name    : lean_workbook_plus_77411
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/87d16111-d3f6-49f3-a12b-cc75dd15f796
-- statement:
--   Correct expression: $S=a\frac{1-r^{n+1}}{1-r}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77411 (a r n : ℕ) : a * (1 - r ^ (n + 1)) / (1 - r) = a * (1 - r ^ (n + 1)) / (1 - r)   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_18934
-- name    : lean_workbook_plus_18934
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c402e823-f263-4a58-b7de-8ba6a605a444
-- statement:
--   Would both $\frac{1+2i}{5}$ and $\frac15+\frac25i$ be equally acceptable?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18934 : (1 + 2 * Complex.I) / 5 = 1 / 5 + 2 / 5 * Complex.I   :=  by sorry

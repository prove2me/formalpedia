-- Prove2me | Theorems.Thm_lean_workbook_plus_20262
-- name    : lean_workbook_plus_20262
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/80835666-4185-4ff0-a0e1-900de048c222
-- statement:
--   Other idea: for $n>1$ we have: $(n+1)^2<n^2+3n<(n+2)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20262 (n : ℕ) (hn : 1 < n) : (n + 1) ^ 2 < n ^ 2 + 3 * n ∧ n ^ 2 + 3 * n < (n + 2) ^ 2   :=  by sorry

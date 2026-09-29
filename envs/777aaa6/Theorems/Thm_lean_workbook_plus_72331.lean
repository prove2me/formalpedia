-- Prove2me | Theorems.Thm_lean_workbook_plus_72331
-- name    : lean_workbook_plus_72331
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/72034c0c-0f63-4205-96db-ee12c05456f0
-- statement:
--   Given the arithmetic sum formula $S=\frac{n(n+1)}{2}$, find the value of $S$ for $n=1000$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72331 (n : ℕ) (hn : n = 1000) : n * (n + 1) / 2 = 500500   :=  by sorry

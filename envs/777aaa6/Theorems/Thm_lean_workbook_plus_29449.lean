-- Prove2me | Theorems.Thm_lean_workbook_plus_29449
-- name    : lean_workbook_plus_29449
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/db046538-f3ba-46d4-a977-1c83d67b4301
-- statement:
--   Prove the sum of squares formula: $1^2+2^2+...+n^2=\frac{n(n+1)(2n+1)}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29449 (n : ℕ) : ∑ i in Finset.range (n+1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_57218
-- name    : lean_workbook_plus_57218
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/fdb51487-db1b-4632-95e6-a3cd77a8e284
-- statement:
--   $\sum_{n=0}^{\infty} 1/{n!} = e$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57218 : ∑' n : ℕ, (1 / n! : ℝ) = Real.exp 1   :=  by sorry

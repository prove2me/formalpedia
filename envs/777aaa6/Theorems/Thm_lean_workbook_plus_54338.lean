-- Prove2me | Theorems.Thm_lean_workbook_plus_54338
-- name    : lean_workbook_plus_54338
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d13a2982-35ca-4cc1-9a52-8666dd31f744
-- statement:
--   For every natural number $n$ such that $n>1$ , is $n+1$ coprime (relatively prime) to $n$? Is there a proof for this?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54338 (n : ℕ) (h : n > 1) : Nat.Coprime (n + 1) n   :=  by sorry

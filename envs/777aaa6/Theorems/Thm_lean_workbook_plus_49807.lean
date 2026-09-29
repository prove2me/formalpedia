-- Prove2me | Theorems.Thm_lean_workbook_plus_49807
-- name    : lean_workbook_plus_49807
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/2ae07208-cbb5-4283-a3fa-5b88a333b6d2
-- statement:
--   Prove that for any finite set of non-negative reals $A$, $1+\sum_{x\in A} x\le \prod_{x\in A}(1+x)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49807 (A : Finset ℝ) (hA : ∀ x ∈ A, 0 ≤ x) :
  1 + ∑ x in A, x ≤ ∏ x in A, (1 + x)   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_53539
-- name    : lean_workbook_plus_53539
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/69a46a1e-7308-43a0-babc-616571d719a1
-- statement:
--   Find the sum $S=1/2+1/4+1/6+1/8+………+1/2n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53539 (n : ℕ) : ∑ k in Finset.range n, (1/(2 * k)) = 1/2 * ∑ k in Finset.range n, (1/k)   :=  by sorry

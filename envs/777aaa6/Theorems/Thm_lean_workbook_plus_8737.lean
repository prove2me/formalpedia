-- Prove2me | Theorems.Thm_lean_workbook_plus_8737
-- name    : lean_workbook_plus_8737
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/c73c79e2-759e-406a-85f3-121ec4783870
-- statement:
--   Prove by induction that $1^{3}+2^{3}+.....+n^{3} \le n^{4} $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8737 (n : ℕ) : ∑ i in Finset.range n, i^3 ≤ n^4   :=  by sorry

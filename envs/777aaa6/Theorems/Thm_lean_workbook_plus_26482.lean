-- Prove2me | Theorems.Thm_lean_workbook_plus_26482
-- name    : lean_workbook_plus_26482
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/e338c0e2-dcbd-4589-badc-620ee400c071
-- statement:
--   Represent every integer $N$ in the form $N=180x+r$ with integers $x$ and $r$ such that $0\le r\le179$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26482 (N : ℤ) : ∃ x r : ℤ, N = 180 * x + r ∧ 0 ≤ r ∧ r ≤ 179   :=  by sorry

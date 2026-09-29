-- Prove2me | Theorems.Thm_lean_workbook_plus_47065
-- name    : lean_workbook_plus_47065
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/9f0d0283-2ed5-424a-8ff3-304cf80cf7db
-- statement:
--   Prove by induction that $\sum_{k=0}^{n-1} p^k < p^n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47065 (p : ℕ) (hp : 1 < p) (n : ℕ) : ∑ k in Finset.range n, p^k < p^n   :=  by sorry

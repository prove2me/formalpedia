-- Prove2me | Theorems.Thm_lean_workbook_plus_13456
-- name    : lean_workbook_plus_13456
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/f2f551cd-4a1a-4701-bee7-e3e077434187
-- statement:
--   Prove that $f(n)\in N$ where $f(n)=\frac{(2n)!}{(n!)^{2}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13456 (n : ℕ) : ∃ k : ℕ, (2 * n)! / (n!)^2 = k   :=  by sorry

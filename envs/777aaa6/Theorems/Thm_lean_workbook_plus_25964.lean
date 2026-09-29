-- Prove2me | Theorems.Thm_lean_workbook_plus_25964
-- name    : lean_workbook_plus_25964
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/aab983e2-215b-488f-808d-b2d2c0e71b37
-- statement:
--   Prove the combinatorial identity: $\sum_{k=0}^{n}{{3n}\choose{3k}}=\frac{1}{3}(8^{n}+2(-1)^{n})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25964 (n : ℕ) : ∑ k in Finset.range (n+1), choose (3*n) (3*k) = (1/3)*(8^n + 2*(-1 : ℤ)^n)   :=  by sorry

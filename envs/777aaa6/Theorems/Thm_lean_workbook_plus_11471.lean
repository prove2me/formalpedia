-- Prove2me | Theorems.Thm_lean_workbook_plus_11471
-- name    : lean_workbook_plus_11471
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/12d29381-2548-4b1a-9fe5-fe356b0a954e
-- statement:
--   Therefore, the answer is $(k-1)!\cdot\frac{(n+k-1)!}{(k-1)!}=\boxed{(n+k-1)!}$ ways.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11471  (k n : ℕ)
  (h₀ : 0 < k ∧ 0 < n) :
  (k - 1)! * (n + k - 1)! / (k - 1)! = (n + k - 1)!   :=  by sorry

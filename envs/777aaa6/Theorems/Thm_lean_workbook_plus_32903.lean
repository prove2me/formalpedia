-- Prove2me | Theorems.Thm_lean_workbook_plus_32903
-- name    : lean_workbook_plus_32903
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c73f491b-bced-403c-9e9f-608b68d0a879
-- statement:
--   If $b+c=0$, prove that $a^{2n+1}+b^{2n+1}+c^{2n+1}=(a+b+c)^{2n+1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32903 (n : ℕ) (a b c : ℤ) (h : b + c = 0) :
  a^(2 * n + 1) + b^(2 * n + 1) + c^(2 * n + 1) = (a + b + c)^(2 * n + 1)   :=  by sorry

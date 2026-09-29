-- Prove2me | Theorems.Thm_lean_workbook_plus_16961
-- name    : lean_workbook_plus_16961
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/bf48d42e-04de-4d27-8e5c-2deca2c380b2
-- statement:
--   Let $n\in N$ And $n\geqq2$. Prove that $n\leqq 2^{n-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16961 (n : ℕ) (_h : 2 ≤ n) : n ≤ 2 ^ (n - 1)   :=  by sorry

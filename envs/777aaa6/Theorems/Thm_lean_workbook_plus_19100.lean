-- Prove2me | Theorems.Thm_lean_workbook_plus_19100
-- name    : lean_workbook_plus_19100
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/cbef16ae-fb7c-4e5f-8f72-6dd3b957499e
-- statement:
--   Hence the total number of concave sequences is at most $2^1 + 2^2 + \ldots + 2^{m-1} + 1 = 2^m-1 <2^m$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19100  (m : ℕ)
  (h₀ : 0 < m) :
  ∑ k in Finset.Icc 1 m, 2^k < 2^m - 1   :=  by sorry

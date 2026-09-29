-- Prove2me | Theorems.Thm_lean_workbook_plus_25618
-- name    : lean_workbook_plus_25618
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d85bf719-6219-4596-9a55-181de6cbbf67
-- statement:
--   Compute $\sum^{10}_{i=1} i^2\binom{10}{i}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25618 : ∑ i in Finset.Icc 1 10, i^2 * (Nat.choose 10 i) = 145   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_23618
-- name    : lean_workbook_plus_23618
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/9233ecff-bc87-4b7c-a438-55b4a5fd8d7b
-- statement:
--   Prove the following: $1+2+4+8...+2^n=2^{n+1}-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23618 : ∀ n : ℕ, ∑ i in Finset.range n, 2 ^ i = 2 ^ (n + 1) - 1   :=  by sorry

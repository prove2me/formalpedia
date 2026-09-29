-- Prove2me | Theorems.Thm_lean_workbook_plus_67012
-- name    : lean_workbook_plus_67012
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/ca2c429e-8926-4ae3-8fe6-df99b9af883d
-- statement:
--   Verify the correctness of the expression $\binom{4}{4} + \binom{5}{4} + \binom{6}{4} + \binom{7}{4} + \binom{8}{4}$ and its evaluation to 112.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67012 (h₁ : 4 ≤ 4 ∧ 4 ≤ 5 ∧ 4 ≤ 6 ∧ 4 ≤ 7 ∧ 4 ≤ 8) : (Nat.choose 4 4 + Nat.choose 5 4 + Nat.choose 6 4 + Nat.choose 7 4 + Nat.choose 8 4) = 112   :=  by sorry

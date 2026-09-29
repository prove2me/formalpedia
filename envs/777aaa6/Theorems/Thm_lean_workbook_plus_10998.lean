-- Prove2me | Theorems.Thm_lean_workbook_plus_10998
-- name    : lean_workbook_plus_10998
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ba68de5e-058a-4958-9bdb-7fa3267a4628
-- statement:
--   Calculate the sum: $\sum^{10}_{k=2}\binom{k}{2}\binom{12-k}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10998 (h₁ : 2 ≤ 10) : ∑ k in Finset.Icc 2 10, (Nat.choose k 2 * Nat.choose (12 - k) 2) = 5148   :=  by sorry

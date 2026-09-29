-- Prove2me | Theorems.Thm_lean_workbook_plus_79765
-- name    : lean_workbook_plus_79765
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/05074afa-a8b3-4a59-9895-b2704ac919a2
-- statement:
--   $2 (\binom{2n+1}{0}+\binom{2n+1}{1}+\binom{2n+1}{2}+...+\binom{2n+1}{n})= 2^{2n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79765 (n : ℕ) : 2 * (∑ k in Finset.range (n+1), (Nat.choose (2 * n + 1) k)) = 2^(2 * n + 1)   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_56430
-- name    : lean_workbook_plus_56430
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/50a7aeca-1357-42da-a254-f0d6aaf35af1
-- statement:
--   $ \binom{n}{3}+\binom{n+k}{3}> \binom{n+1}{3}+\binom{n+k-1}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56430 ∀ n k : ℕ, n > 0 ∧ k > 0 → (n.choose 3 + (n + k).choose 3) > (n + 1).choose 3 + (n + k - 1).choose 3   :=  by sorry

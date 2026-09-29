-- Prove2me | Theorems.Thm_lean_workbook_plus_63619
-- name    : lean_workbook_plus_63619
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/a109bdb9-7005-4b99-a2d1-68b806b5ce44
-- statement:
--   If $n=2p+1$ is odd, show that $2^n+1$ is divisible by 3.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63619 : ∀ n : ℕ, n = 2 * p + 1 → 3 ∣ (2 ^ n + 1)   :=  by sorry

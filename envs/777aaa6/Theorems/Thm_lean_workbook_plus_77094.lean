-- Prove2me | Theorems.Thm_lean_workbook_plus_77094
-- name    : lean_workbook_plus_77094
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a0409f70-25b1-41f5-af4e-0c8cf40ab74f
-- statement:
--   If $n\le k$ are positive integers, then $2^n\pmod{10^k}$ is always divisible by $2^k$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77094 : ∀ n k : ℕ, n ≤ k → 2 ^ k ∣ 2 ^ n % 10 ^ k   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_53094
-- name    : lean_workbook_plus_53094
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/7f80fccb-64e3-41e9-984d-2991ebd81eb6
-- statement:
--   If $n$ is odd, then $5|1^n+4^n,5|2^n+3^n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53094 (n : ℕ) : n % 2 = 1 → 5 ∣ 1 ^ n + 4 ^ n ∧ 5 ∣ 2 ^ n + 3 ^ n   :=  by sorry

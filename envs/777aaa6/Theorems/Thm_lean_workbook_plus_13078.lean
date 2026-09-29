-- Prove2me | Theorems.Thm_lean_workbook_plus_13078
-- name    : lean_workbook_plus_13078
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/c96e377e-ecb8-49c2-ad82-8ba318b6245b
-- statement:
--   Prove that for every positive integer $n$ there are positive integers $a$ and $b$ exist with $n | 4a^2 + 9b^2 -1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13078 (n : ℕ) : ∃ a b : ℕ, n ∣ 4*a^2 + 9*b^2 - 1   :=  by sorry

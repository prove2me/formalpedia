-- Prove2me | Theorems.Thm_lean_workbook_plus_64020
-- name    : lean_workbook_plus_64020
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5bfbaa81-c522-4764-9000-9d79f382b721
-- statement:
--   Given that $ a $ is a prime number greater than 5, prove that at least one of $ \{a-3,a-1,a+1\}$ is divisible by 3.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64020 (p : ℕ) (hp : 5 < p) (hp2 : Nat.Prime p) : 3 ∣ p - 3 ∨ 3 ∣ p - 1 ∨ 3 ∣ p + 1   :=  by sorry

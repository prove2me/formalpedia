-- Prove2me | Theorems.Thm_lean_workbook_plus_7674
-- name    : lean_workbook_plus_7674
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/dc40e318-3957-4fd8-a723-2f221c4d51f5
-- statement:
--   prove that $10^{4n}-1$ is divisible by $10^{4}-1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7674 (n : ℕ) : 10 ^ 4 - 1 ∣ 10 ^ (4 * n) - 1   :=  by sorry

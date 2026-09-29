-- Prove2me | Theorems.Thm_lean_workbook_plus_27480
-- name    : lean_workbook_plus_27480
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/163f3864-0ad5-4706-a03f-0fc048ef0b98
-- statement:
--   Prove that for any integer the number $2n^3+3n^2+7n$ is divisible by $6$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27480 : ∀ n : ℤ, 6 ∣ 2*n^3+3*n^2+7*n   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_81164
-- name    : lean_workbook_plus_81164
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/da198df9-1daa-4203-8c13-530e90296961
-- statement:
--   Prove that if $n$ is even, $4^{n}+2^{n}+1$ is divisible by 3.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81164 : ∀ n : ℕ, Even n → 3 ∣ (4^n + 2^n + 1)   :=  by sorry

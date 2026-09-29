-- Prove2me | Theorems.Thm_lean_workbook_plus_61163
-- name    : lean_workbook_plus_61163
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/7adb686a-4348-43c0-b644-eae54374c80b
-- statement:
--   Prove that if $x$ is even, then $2^x - 1$ is divisible by 3.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61163 : ∀ x : ℕ, Even x → 3 ∣ (2 ^ x - 1)   :=  by sorry

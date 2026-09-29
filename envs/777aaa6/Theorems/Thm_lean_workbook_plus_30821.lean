-- Prove2me | Theorems.Thm_lean_workbook_plus_30821
-- name    : lean_workbook_plus_30821
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/3cbbb409-dda3-49b7-b445-ba479b6220e6
-- statement:
--   Prove that if m is divisible by 7 (but not equal to 7), then ${m \choose 7}$ is not divisible by m.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30821 : ∀ m : ℕ, 7 ∣ m ∧ m ≠ 7 → ¬ (m ∣ choose m 7)   :=  by sorry

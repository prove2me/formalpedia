-- Prove2me | Theorems.Thm_lean_workbook_plus_65246
-- name    : lean_workbook_plus_65246
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/169824ac-cc0c-4d8f-bb5e-42f2b0f4e29f
-- statement:
--   If the three-digit number $ABC$ is divisible by $27$ , prove that the three-digit numbers $BCA$ and $CAB$ are also divisible by $27$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65246 (A B C : ℕ) (hA : A ≤ 9 ∧ B ≤ 9 ∧ C ≤ 9) (h : 27 ∣ (100 * A + 10 * B + C)) : 27 ∣ (100 * B + 10 * C + A) ∧ 27 ∣ (100 * C + 10 * A + B)   :=  by sorry

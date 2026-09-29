-- Prove2me | Theorems.Thm_lean_workbook_plus_20498
-- name    : lean_workbook_plus_20498
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/61b57303-af6c-4acd-83cc-edf0f46f1f94
-- statement:
--   $\frac{27}{11} = 2\frac{5}{11} = 2\frac{340}{748}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20498 (a b c : ℚ) (h₁ : a = 27 / 11) (h₂ : b = 2 + 5 / 11) (h₃ : c = 2 + 340 / 748) : a = b ∧ b = c   :=  by sorry

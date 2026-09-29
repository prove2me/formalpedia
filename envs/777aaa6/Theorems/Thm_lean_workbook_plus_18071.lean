-- Prove2me | Theorems.Thm_lean_workbook_plus_18071
-- name    : lean_workbook_plus_18071
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/03dbffc1-2456-4903-a432-67b6b335951d
-- statement:
--   Prove that $ \tan x$ is increasing on $ \Big]-\frac\pi2,\frac\pi2\Big[$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18071 : ∀ x y : ℝ, x ∈ Set.Ioo (-π / 2) (π / 2) ∧ y ∈ Set.Ioo (-π / 2) (π / 2) ∧ x < y → tan x < tan y   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_72779
-- name    : lean_workbook_plus_72779
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/fb4bcfa2-1b3c-48f5-b62e-3f8fb12eaec8
-- statement:
--   If $x=y=0$, what is $x^{4} + y^{4}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72779 (x y : ℝ) (h₁ : x = 0) (h₂ : y = 0) : x^4 + y^4 = 0   :=  by sorry

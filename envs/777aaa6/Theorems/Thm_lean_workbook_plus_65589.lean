-- Prove2me | Theorems.Thm_lean_workbook_plus_65589
-- name    : lean_workbook_plus_65589
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/4db36728-e2fa-410a-9523-9aead47dc0c6
-- statement:
--   If $x_1+x_2=-a$ and $x_2+x_3=-b$ , then $x_1-x_3=b-a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65589 (x₁ x₂ x₃ a b : ℝ) (h₁ : x₁ + x₂ = -a) (h₂ : x₂ + x₃ = -b) : x₁ - x₃ = b - a   :=  by sorry

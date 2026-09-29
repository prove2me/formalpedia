-- Prove2me | Theorems.Thm_lean_workbook_plus_65617
-- name    : lean_workbook_plus_65617
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5c8caed0-ac14-4f26-ad3c-6ab21ab66dbb
-- statement:
--   Find the hypotenuse of a right triangle whose legs are $20806$ and $408$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65617 (a b c : ℝ) (h₁ : a = 20806) (h₂ : b = 408) (h₃ : c^2 = a^2 + b^2) : c = 20874   :=  by sorry

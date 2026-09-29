-- Prove2me | Theorems.Thm_lean_workbook_plus_59729
-- name    : lean_workbook_plus_59729
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5ed8f5b1-98d0-4716-a8fd-50bdb5d8d2c7
-- statement:
--   The radical sign is defined as the positive square root, ie $ |x|=\sqrt{x^2}$ , for all real values of $ x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59729 : ∀ x : ℝ, abs x = Real.sqrt (x ^ 2)   :=  by sorry

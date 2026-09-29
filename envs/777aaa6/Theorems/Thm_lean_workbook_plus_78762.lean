-- Prove2me | Theorems.Thm_lean_workbook_plus_78762
-- name    : lean_workbook_plus_78762
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/f723938e-8351-419e-89c3-39535f684110
-- statement:
--   Prove $\dfrac{1}{2}[(a-b)^2+(b-c)^2+(c-a)^2] \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78762 : ∀ a b c : ℝ, (1/2)*((a-b)^2 + (b-c)^2 + (c-a)^2) ≥ 0   :=  by sorry

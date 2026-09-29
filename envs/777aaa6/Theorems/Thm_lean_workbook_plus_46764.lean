-- Prove2me | Theorems.Thm_lean_workbook_plus_46764
-- name    : lean_workbook_plus_46764
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/257a7203-ba86-4183-b2e1-289d2f824c25
-- statement:
--   Does the condition $x \geq y$ hold when $y = \frac{x}{2}$ and $y > 0$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46764 (x y : ℝ) (h₁ : y = x / 2) (h₂ : y > 0) : x ≥ y   :=  by sorry

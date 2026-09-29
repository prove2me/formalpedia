-- Prove2me | Theorems.Thm_lean_workbook_plus_65999
-- name    : lean_workbook_plus_65999
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/80373cf5-7753-4836-b09d-81e1dbc4ea69
-- statement:
--   Which of the following is /are true?\n1. Every linear transformation from $\mathbb{R}^2$ to $\mathbb{R}^2$ maps lines onto points or lines\n2. Every surjective linear transformation from $\mathbb{R}^2$ to $\mathbb{R}^2$ maps lines onto lines.\n3. Every bijective linear transformation from $\mathbb{R}^2$ to $\mathbb{R}^2$ maps pairs of parallel lines to pairs of parallel lines.\n4. Every bijective linear transformation from $\mathbb{R}^2$ to $\mathbb{R}^2$ maps pairs of perpendicular lines to pairs of perpendicular lines.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65999 (f : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) : (∀ v : ℝ × ℝ, ∃ a b : ℝ, v = (a, b)) ∨ (∀ v : ℝ × ℝ, ∃ a b : ℝ, v = (a, b) ∨ v = (b, -a))   :=  by sorry

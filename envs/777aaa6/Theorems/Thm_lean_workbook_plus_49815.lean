-- Prove2me | Theorems.Thm_lean_workbook_plus_49815
-- name    : lean_workbook_plus_49815
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/587f49a4-c3cc-4967-b4f4-88d12b9e08de
-- statement:
--   When $a\geq b\geq c$ or $b\geq c\geq a$ or $c\geq a\geq b$ we have that $(a-b)(b-c)(c-a)\leq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49815 (a b c : ℝ) (h : a ≥ b ∧ b ≥ c ∨ b ≥ c ∧ c ≥ a ∨ c ≥ a ∧ a ≥ b) : (a - b) * (b - c) * (c - a) ≤ 0   :=  by sorry

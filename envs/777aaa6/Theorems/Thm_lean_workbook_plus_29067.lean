-- Prove2me | Theorems.Thm_lean_workbook_plus_29067
-- name    : lean_workbook_plus_29067
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/3330b48f-f0d7-4cb3-be57-37afddb3630a
-- statement:
--   Let $0\leq a \leq b \leq c$ be real numbers. Prove that $(a+3b)(b+4c)(c+2a) \geq 60abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29067 (a b c : ℝ) (h1: 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) (h2: a ≤ b ∧ b ≤ c) : (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c   :=  by sorry

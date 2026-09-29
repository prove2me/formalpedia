-- Prove2me | Theorems.Thm_lean_workbook_plus_52267
-- name    : lean_workbook_plus_52267
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/0a4bf476-1034-41d6-b7dd-4013ff747531
-- statement:
--   Prove that $x(1-x)(x^{2}+x+1)(x^{2}-x+1)>0$ for $x\in \mathbb{R}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52267 : ∀ x : ℝ, x * (1 - x) * (x^2 + x + 1) * (x^2 - x + 1) > 0   :=  by sorry

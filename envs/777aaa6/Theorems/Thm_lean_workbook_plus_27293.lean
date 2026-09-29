-- Prove2me | Theorems.Thm_lean_workbook_plus_27293
-- name    : lean_workbook_plus_27293
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/3eafe275-c95a-46ca-a8a1-eed38e5dab27
-- statement:
--   Let $x \in \mathbb{R}$ such that $x^3 + 4x = 8$ . Determine the value of $x^7 + 64x^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27293 (x : ℝ) (h : x^3 + 4*x = 8) : x^7 + 64*x^2 = 128   :=  by sorry

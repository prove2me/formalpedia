-- Prove2me | Theorems.Thm_lean_workbook_plus_58326
-- name    : lean_workbook_plus_58326
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/928476a7-46fc-4834-89af-7942bf14b595
-- statement:
--   Prove that if $x^2 + y^2 = 1$ and $x, y \geq 0$, then $x + y \leq \sqrt{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58326 (x y : ℝ) (h₁ : x ≥ 0 ∧ y ≥ 0) (h₂ : x ^ 2 + y ^ 2 = 1) : x + y ≤ Real.sqrt 2   :=  by sorry

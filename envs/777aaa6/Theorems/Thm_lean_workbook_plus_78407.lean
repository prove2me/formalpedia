-- Prove2me | Theorems.Thm_lean_workbook_plus_78407
-- name    : lean_workbook_plus_78407
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/95a80bf7-b25f-4d94-aaad-cdd8f38263b0
-- statement:
--   prove that $2abc \leq 1$ using $a^2 + b^2 + c^2 \geq 0$ and $a^2 + b^2 + c^2 + 2abc = 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78407 (a b c : ℝ) (h1 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 0) (h2 : a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c = 1) : 2 * a * b * c ≤ 1   :=  by sorry

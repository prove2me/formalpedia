-- Prove2me | Theorems.Thm_lean_workbook_plus_49523
-- name    : lean_workbook_plus_49523
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/919459b3-d5c7-4d63-9439-627fb5850a01
-- statement:
--   Let $a,b,c$ are real numbers,prove that: $(a^2+b^2+c^2)^2\geq (a+b+c)(a^2b+b^2c+c^2a).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49523 (a b c : ℝ): (a^2 + b^2 + c^2)^2 ≥ (a+b+c)*(a^2 * b + b^2 * c + c^2 * a)   :=  by sorry

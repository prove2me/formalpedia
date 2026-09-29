-- Prove2me | Theorems.Thm_lean_workbook_plus_50409
-- name    : lean_workbook_plus_50409
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/f7037d34-0d5c-4915-a0e9-cfe76d835bf9
-- statement:
--   Prove that \((a+b+c)^2\geq3(ab+ac+bc)\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50409 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (a * b + a * c + b * c)   :=  by sorry

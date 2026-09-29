-- Prove2me | Theorems.Thm_lean_workbook_plus_44548
-- name    : lean_workbook_plus_44548
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/e7bc863e-2605-44d1-8bfa-59487f8291a1
-- statement:
--   Can the sine of a sum be expressed as $\sin(123) = \sin(100)\cos(23) + \sin(23)\cos(100)$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44548 : sin (123 : ℝ) = sin (100 : ℝ) * cos (23 : ℝ) + sin (23 : ℝ) * cos (100 : ℝ)   :=  by sorry

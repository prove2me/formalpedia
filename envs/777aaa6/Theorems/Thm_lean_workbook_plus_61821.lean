-- Prove2me | Theorems.Thm_lean_workbook_plus_61821
-- name    : lean_workbook_plus_61821
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/961de777-9a3d-44f8-91e6-2d6ccbfb3154
-- statement:
--   Prove that $\sin(a+b+c) \sin b = \sin(a+b) \sin (b+c) - \sin a \sin c$ (corrected).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61821 (a b c : ℝ) : sin (a + b + c) * sin b = sin (a + b) * sin (b + c) - sin a * sin c   :=  by sorry

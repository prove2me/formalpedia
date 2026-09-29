-- Prove2me | Theorems.Thm_lean_workbook_plus_8917
-- name    : lean_workbook_plus_8917
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/70f23897-5ea2-4fee-844a-28ca8330d5a8
-- statement:
--   Derive the sine of the sum of two angles formula: $\sin(A + B) = \sin(A)\cos(B) + \cos(A)\sin(B)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8917 (A B : ℝ) : sin (A + B) = sin A * cos B + cos A * sin B   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_33814
-- name    : lean_workbook_plus_33814
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/7faa8836-5fde-49b5-94f6-ff8c3bedb9e9
-- statement:
--   Prove that $$cos(A-B)=cosAcosB+sinAsinB$$ using vector algebra.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33814 (A B : ℝ) : Real.cos (A - B) = Real.cos A * Real.cos B + Real.sin A * Real.sin B   :=  by sorry

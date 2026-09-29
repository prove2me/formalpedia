-- Prove2me | Theorems.Thm_lean_workbook_plus_11506
-- name    : lean_workbook_plus_11506
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/14bc8537-b595-4926-abcd-5db199cef0d0
-- statement:
--   Prove that $\cos^2 A + \cos^2 B + \cos^2 C = 1 - 2 \cdot \cos A \cdot \cos B \cdot \cos C$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11506 : ∀ A B C : ℝ, Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 = 1 - 2 * Real.cos A * Real.cos B * Real.cos C   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_33724
-- name    : lean_workbook_plus_33724
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/a6b9e895-5b58-4ebe-8b4c-1d4b26866693
-- statement:
--   In triangle,prove \n $2/3\,\cos \left( A \right) +2/3\,\cos \left( B \right) +2/3\,\cos \left( C \right) \geq \left( \cos \left( B \right) +\cos \left( C \right) \right) \left( \cos \left( C \right) +\cos \left( A \right) \right) \left( \cos \left( A \right) +\cos \left( B \right) \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33724 : ∀ A B C : ℝ, 2 / 3 * Real.cos A + 2 / 3 * Real.cos B + 2 / 3 * Real.cos C ≥ (Real.cos B + Real.cos C) * (Real.cos C + Real.cos A) * (Real.cos A + Real.cos B)   :=  by sorry

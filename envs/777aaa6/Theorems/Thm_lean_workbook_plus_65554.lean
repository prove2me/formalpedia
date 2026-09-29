-- Prove2me | Theorems.Thm_lean_workbook_plus_65554
-- name    : lean_workbook_plus_65554
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/af082143-baa0-409d-9c0c-f220bcb48807
-- statement:
--   If $A$ is an invertible matrix, prove that $A^TA$ is invertible and find its inverse.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65554 (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : IsUnit A) : IsUnit (A^T * A)   :=  by sorry

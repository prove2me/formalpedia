-- Prove2me | Theorems.Thm_lean_workbook_plus_34790
-- name    : lean_workbook_plus_34790
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/590b737f-5ed2-49c1-8fbc-98b6d2b6f0fd
-- statement:
--   Construct a matrix with integer coefficients and non-zero determinant, not necessarily $\pm1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34790 : ∃ A : Matrix (Fin 2) (Fin 2) ℤ, A.det ≠ 0   :=  by sorry

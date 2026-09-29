-- Prove2me | Theorems.Thm_lean_workbook_plus_45992
-- name    : lean_workbook_plus_45992
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/1e5f77a0-f22c-49b1-aba1-fbd3d4b0baac
-- statement:
--   Let $P(x)=\det(A-xI_n).$ This is a polynomial from $\mathbb{R}[X].$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45992 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : ∃ P : ℝ → ℝ, P = fun x ↦ Matrix.det (A - x • (1 : Matrix (Fin n) (Fin n) ℝ))   :=  by sorry

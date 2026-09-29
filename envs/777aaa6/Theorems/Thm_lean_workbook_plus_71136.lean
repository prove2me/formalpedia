-- Prove2me | Theorems.Thm_lean_workbook_plus_71136
-- name    : lean_workbook_plus_71136
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/3b860cbb-2b5d-4246-8fdf-79d80507325f
-- statement:
--   If $x$ and $y$ are two reals such that $-1 < x < 0$ and $0 < y < 1$ , prove that $x^{2}+xy+y^{2} < 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71136 (x y : ℝ) (hx : -1 < x ∧ x < 0) (hy : 0 < y ∧ y < 1) :
  x^2 + x*y + y^2 < 1   :=  by sorry

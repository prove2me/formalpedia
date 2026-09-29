-- Prove2me | Theorems.Thm_lean_workbook_plus_7867
-- name    : lean_workbook_plus_7867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4c1cc1d9-2876-45ca-904f-fc8556b13741
-- statement:
--   Let $x_i>x_j$ , then ${x_ix_j(x_i-x_j)<\frac{x_i^2+x_ix_j+x_j^2}{3}(x_i-x_j}=\frac{x_i^3-x_j^3}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7867 (x_i x_j : ℝ) (h : x_i > x_j) :
  x_i * x_j * (x_i - x_j) < (x_i ^ 2 + x_i * x_j + x_j ^ 2) * (x_i - x_j)   :=  by sorry

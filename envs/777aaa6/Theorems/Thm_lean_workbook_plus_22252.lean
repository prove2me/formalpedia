-- Prove2me | Theorems.Thm_lean_workbook_plus_22252
-- name    : lean_workbook_plus_22252
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b1a69631-fe51-4a43-b065-cc3cc132e2f0
-- statement:
--   Let $c \in \mathbb{Z}$ and $f(X)$ a polynomial in $\mathbb{Z}[X]$ of non zero degree,then their product has non zero degree.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22252 (c : ℤ) (f : Polynomial ℤ) (hf : f.degree ≠ 0) : (c * f).degree ≠ 0   :=  by sorry

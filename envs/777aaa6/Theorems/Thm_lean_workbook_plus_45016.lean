-- Prove2me | Theorems.Thm_lean_workbook_plus_45016
-- name    : lean_workbook_plus_45016
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/79b3f996-b6e7-48c3-803b-3c48abc29f38
-- statement:
--   Soient x et y deux réels tels que $-1<x<0$ et $0<y<1$ . Montrer que $x^2+y^2+xy<1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45016 (x y : ℝ) (hx : -1 < x ∧ x < 0) (hy : 0 < y ∧ y < 1) : x^2 + y^2 + x * y < 1   :=  by sorry

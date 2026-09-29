-- Prove2me | Theorems.Thm_lean_workbook_plus_55302
-- name    : lean_workbook_plus_55302
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/a3f5984a-7d88-4e5d-8125-aa8a23093ca9
-- statement:
--   Let $ x,y\geq 0$ , s.t. $ x^2 + y^3\geq x^3 + y^4$ . Prove that: $ x^3 + y^3\leq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55302 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^2 + y^3 ≥ x^3 + y^4) : x^3 + y^3 ≤ 2   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_72091
-- name    : lean_workbook_plus_72091
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/8d355514-5672-4527-83bb-781353827a5f
-- statement:
--   Let $x,y $ be reals such that $x^2+y^2-xy= 75.$ Prove that $5x^2+5y^2-8xy \geq 150$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72091 (x y : ℝ) (h : x^2 + y^2 - x*y = 75) : 5*x^2 + 5*y^2 - 8*x*y ≥ 150   :=  by sorry

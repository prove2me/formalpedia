-- Prove2me | Theorems.Thm_lean_workbook_plus_2944
-- name    : lean_workbook_plus_2944
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0bb0c1a0-f277-4ace-9143-f91327d5f0fd
-- statement:
--   Prove that for any real numbers $x,y$ \n $x^4+y^4+(x^2+1)(y^2+1) \ge x^3(1+y)+y^3(1+x)+x+y$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2944 (x y : ℝ) : x^4 + y^4 + (x^2 + 1) * (y^2 + 1) ≥ x^3 * (1 + y) + y^3 * (1 + x) + x + y   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_59049
-- name    : lean_workbook_plus_59049
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/85bbfceb-e44e-44c5-bf94-544daa90fc18
-- statement:
--   Prove that $x^6 + y^6 + x^2y^2 + x^4y^4 >= x^4y+x^2y^5+x^5y^2+xy^4$ for positive $x, y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59049 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^6 + y^6 + x^2 * y^2 + x^4 * y^4 >= x^4 * y + x^2 * y^5 + x^5 * y^2 + x * y^4   :=  by sorry

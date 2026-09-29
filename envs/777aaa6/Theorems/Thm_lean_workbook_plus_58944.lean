-- Prove2me | Theorems.Thm_lean_workbook_plus_58944
-- name    : lean_workbook_plus_58944
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/015b3721-d1dc-445d-aff9-b2782dd9a10a
-- statement:
--   Prove that $\\frac{1}{1+x^2}+\\frac{1}{1+y^2}\\le \\frac{2}{1+xy}$ given $x,y\\ge 0$ and $xy\\le 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58944 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x * y ≤ 1) : 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) ≤ 2 / (1 + x * y)   :=  by sorry

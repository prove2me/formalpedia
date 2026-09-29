-- Prove2me | Theorems.Thm_lean_workbook_plus_32251
-- name    : lean_workbook_plus_32251
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/480c7873-7e3b-4c0e-ae08-1dd8e0796a7d
-- statement:
--   If $x + \dfrac{1}{y} = \dfrac{1}{5}$ and $y + \dfrac{1}{x} = 20$ , what is the value of the product $xy$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32251 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + 1/y = 1/5) (hxy : y + 1/x = 20) : x*y = 1   :=  by sorry

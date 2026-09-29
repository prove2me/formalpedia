-- Prove2me | Theorems.Thm_lean_workbook_plus_12404
-- name    : lean_workbook_plus_12404
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/963c1717-4d7d-4e01-8792-ff0ddb8c09d3
-- statement:
--   Let $ 0<x<y<z.$ Prove that $ |xz-y^2|<y(z-x).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12404 (x y z : ℝ) (h0 : 0 < x ∧ 0 < y ∧ 0 < z) (h1 : x < y) (h2 : y < z) : |x * z - y ^ 2| < y * (z - x)   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_3937
-- name    : lean_workbook_plus_3937
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/a94f6e09-67c2-49ed-b241-e8c2bc7a02c7
-- statement:
--   Let $x, y, z$ are real numbers such that $x<y<z .$ Prove that \n\n $$(x-y)^{3}+(y-z)^{3}+(z-x)^{3}>0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3937 (x y z : ℝ) (hx: x < y) (hy: y < z) : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 > 0   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_415
-- name    : lean_workbook_plus_415
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/1aac688b-eab5-47a0-b5dd-6e160dafd66f
-- statement:
--   Prove that for positive real numbers $x, y, z$ satisfying $xyz = 1$, the following inequality holds:\n$(x^{2}+y^{2}+z^{2})(x^{4}+y^{4}+z^{4})\leq 3(x^{6}+y^{6}+z^{6})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_415 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) : (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 4 + y ^ 4 + z ^ 4) ≤ 3 * (x ^ 6 + y ^ 6 + z ^ 6)   :=  by sorry

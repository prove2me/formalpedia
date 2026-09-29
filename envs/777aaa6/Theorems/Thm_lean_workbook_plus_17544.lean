-- Prove2me | Theorems.Thm_lean_workbook_plus_17544
-- name    : lean_workbook_plus_17544
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/09c11e91-534a-4072-9a66-ee2a2645d5bf
-- statement:
--   Let $x,y,z$ be positive real numbers. Prove that $(x^{2}+y^{2})(y^{2}+z^{2})(z^{2}+x^{2})\geq(x^{2}+2y^{2}-z^{2})(y^{2}+2z^{2}-x^{2})(z^{2}+2x^{2}-y^{2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17544 (x y z : ℝ) : (x ^ 2 + y ^ 2) * (y ^ 2 + z ^ 2) * (z ^ 2 + x ^ 2) ≥ (x ^ 2 + 2 * y ^ 2 - z ^ 2) * (y ^ 2 + 2 * z ^ 2 - x ^ 2) * (z ^ 2 + 2 * x ^ 2 - y ^ 2)   :=  by sorry

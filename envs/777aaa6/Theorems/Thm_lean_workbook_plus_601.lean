-- Prove2me | Theorems.Thm_lean_workbook_plus_601
-- name    : lean_workbook_plus_601
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/355ce235-1ea0-47c7-adcf-42da9c25d19f
-- statement:
--   Prove that $(x^{30}+y^{30})(y^{30}+z^{30})(z^{30}+x^{30})(x^3+y^3)(y^3+z^3)(z^3+x^3) \geq (x^4+y^4)(y^4+z^4)(z^4+x^4)(x^{29}+y^{29})(y^{29}+z^{29})(z^{29}+x^{29})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_601 ∀ x y z : ℝ, (x ^ 30 + y ^ 30) * (y ^ 30 + z ^ 30) * (z ^ 30 + x ^ 30) * (x ^ 3 + y ^ 3) * (y ^ 3 + z ^ 3) * (z ^ 3 + x ^ 3) ≥ (x ^ 4 + y ^ 4) * (y ^ 4 + z ^ 4) * (z ^ 4 + x ^ 4) * (x ^ 29 + y ^ 29) * (y ^ 29 + z ^ 29) * (z ^ 29 + x ^ 29)   :=  by sorry

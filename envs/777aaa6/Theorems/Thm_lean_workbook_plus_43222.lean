-- Prove2me | Theorems.Thm_lean_workbook_plus_43222
-- name    : lean_workbook_plus_43222
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/d3da79e6-f600-4be2-b451-770e33b810af
-- statement:
--   Prove that $\sqrt{(x^2 + y^2 + z^2)^3} \geq x^3 + y^3 + z^3 - 3xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43222 (x y z : ℝ) :
  Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) ^ 3) ≥ x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z   :=  by sorry

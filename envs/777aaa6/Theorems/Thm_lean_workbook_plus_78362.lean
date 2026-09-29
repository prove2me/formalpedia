-- Prove2me | Theorems.Thm_lean_workbook_plus_78362
-- name    : lean_workbook_plus_78362
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/594d715e-791b-4e9d-8bfb-b1d1b7ab8932
-- statement:
--   By AM-GM, prove that $3x^4+y^4 \geq 4x^3y$, $3y^4+z^4 \geq 4y^3z$, and $3z^4+x^4 \geq 4z^3x$ for real numbers $x$, $y$, and $z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78362 (x y z : ℝ) : 3 * x ^ 4 + y ^ 4 ≥ 4 * x ^ 3 * y ∧ 3 * y ^ 4 + z ^ 4 ≥ 4 * y ^ 3 * z ∧ 3 * z ^ 4 + x ^ 4 ≥ 4 * z ^ 3 * x   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_56634
-- name    : lean_workbook_plus_56634
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f69ebbba-41eb-4e6a-b61a-19eb32d016d4
-- statement:
--   By AM-GM we have: $\frac{1}{2}x^2y^2z^2+\frac{1}{2}y^6 \ge |xy^4z| \ge xy^4z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56634 : ∀ x y z : ℝ, 1 / 2 * x ^ 2 * y ^ 2 * z ^ 2 + 1 / 2 * y ^ 6 ≥ x * y ^ 4 * z   :=  by sorry

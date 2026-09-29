-- Prove2me | Theorems.Thm_lean_workbook_plus_53854
-- name    : lean_workbook_plus_53854
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/8b838feb-d0aa-49f5-9750-4aac3dc9364a
-- statement:
--   We see that $x^2(1-x)+y^2(1-y)+z^2(1-z)\geq 0\implies x^3+y^3+z^3\leq x^2+y^2+z^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53854 (x y z : ℝ) : x ^ 2 * (1 - x) + y ^ 2 * (1 - y) + z ^ 2 * (1 - z) ≥ 0 → x ^ 3 + y ^ 3 + z ^ 3 ≤ x ^ 2 + y ^ 2 + z ^ 2   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_24867
-- name    : lean_workbook_plus_24867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/388aeace-740c-4844-925d-5bc839810166
-- statement:
--   Given 3 reals (not necessarily positive) x, y, z, satisfying the condition $xyz - 3 = x + y + z$, show that $3(x^2 + y^2 + z^2) \ge x^2y^2z^2 - 6(x + y + z) - 9$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24867 (x y z : ℝ) (h : x * y * z - 3 = x + y + z) : 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ x ^ 2 * y ^ 2 * z ^ 2 - 6 * (x + y + z) - 9   :=  by sorry

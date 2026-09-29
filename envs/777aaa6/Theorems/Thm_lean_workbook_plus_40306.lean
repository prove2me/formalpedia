-- Prove2me | Theorems.Thm_lean_workbook_plus_40306
-- name    : lean_workbook_plus_40306
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a6eb43ef-7a96-4252-97ae-b316a2856e9d
-- statement:
--   Prove that the function $f(x) = x^4 + x^2 + ax - 2$ with $a > 0$ is strictly increasing on the interval $(0,1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40306 (a : ℝ) (ha : a > 0) (x y : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hxy : x < y) : (x^4 + x^2 + a * x - 2) < (y^4 + y^2 + a * y - 2)   :=  by sorry

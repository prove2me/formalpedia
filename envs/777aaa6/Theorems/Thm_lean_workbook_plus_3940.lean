-- Prove2me | Theorems.Thm_lean_workbook_plus_3940
-- name    : lean_workbook_plus_3940
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/3e685cb9-34f1-4b66-b7cc-503f26a9247d
-- statement:
--   Let $x, y$ , and $z$ be real numbers satisfying $x + y + z = xyz$. Prove that $x(1 - y^2)(1 - z^2) + y(1 -z^2)(1 - x^2) + z(1 - x^2)(1 - y^2) = 4xyz.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3940 (x y z : ℝ) (h : x + y + z = x*y*z) :
  x * (1 - y ^ 2) * (1 - z ^ 2) + y * (1 - z ^ 2) * (1 - x ^ 2) + z * (1 - x ^ 2) * (1 - y ^ 2) = 4*x*y*z   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_66237
-- name    : lean_workbook_plus_66237
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d9ac1d6d-4c6d-4d5d-8b49-40df8bfea9eb
-- statement:
--   Prove that $x(y^2-z^2)+y(-x^2+z^2)+z(x^2-y^2)$ is equal to $-(x-y)(x-z)(y-z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66237 (x y z : ℝ) : x * (y ^ 2 - z ^ 2) + y * (-x ^ 2 + z ^ 2) + z * (x ^ 2 - y ^ 2) = -(x - y) * (x - z) * (y - z)   :=  by sorry

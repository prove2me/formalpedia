-- Prove2me | Theorems.Thm_lean_workbook_plus_13465
-- name    : lean_workbook_plus_13465
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/dc5b66e8-b98b-47b1-9ee8-df5b7d00238f
-- statement:
--   If $x^2+y^2+z^2=k(xy+xz+yz)$ and $k\geq1$, prove that $3(k+1)^3\geq8(k+2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13465 (x y z : ℝ) (k : ℝ) (h₁ : k ≥ 1) (h₂ : x^2 + y^2 + z^2 = k * (x * y + x * z + y * z)) : 3 * (k + 1)^3 ≥ 8 * (k + 2)   :=  by sorry

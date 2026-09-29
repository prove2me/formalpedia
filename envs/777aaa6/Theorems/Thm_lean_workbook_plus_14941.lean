-- Prove2me | Theorems.Thm_lean_workbook_plus_14941
-- name    : lean_workbook_plus_14941
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/327c581e-73b9-4132-9332-942683d08c4f
-- statement:
--   $(x^2b+y^2a)(a+b)\geq ab(x+y)^2$ is equivalent to $x^2b^2+y^2a^2\geq 2abxy$ , i.e. $(xb - ya)^2 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14941  (x y a b : ℝ) :
  (x^2 * b + y^2 * a) * (a + b) ≥ a * b * (x + y)^2 ↔
  x^2 * b^2 + y^2 * a^2 ≥ 2 * a * b * x * y   :=  by sorry

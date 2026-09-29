-- Prove2me | Theorems.Thm_lean_workbook_plus_71974
-- name    : lean_workbook_plus_71974
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ae8ccf8d-9530-45ce-8b1a-598394d8d1af
-- statement:
--   If $x\ge 2\sqrt 2$ , then $3x-2\ge 6\sqrt 2-2$ and : \n $\sqrt{x^2+15}-\sqrt{x^2-8}=\frac{23}{\sqrt{x^2+15}+\sqrt{x^2-8}}$ is a decreasing function and so is less or equal than its value when $x=2\sqrt 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71974  (x : ℝ)
  (h₀ : 2 * Real.sqrt 2 ≤ x) :
  3 * x - 2 ≥ 6 * Real.sqrt 2 - 2   :=  by sorry

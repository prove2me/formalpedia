-- Prove2me | Theorems.Thm_lean_workbook_plus_80703
-- name    : lean_workbook_plus_80703
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/05ca1d31-a50b-40a6-8ffb-66b8a02d8972
-- statement:
--   $\cos{x}\sin{y}=\frac{1}{2}\cdot\left[\sin{\left(x+y\right)}-\sin{\left(x-y\right)}\right]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80703 : ∀ x y : ℝ, cos x * sin y = 1 / 2 * (sin (x + y) - sin (x - y))   :=  by sorry

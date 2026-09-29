-- Prove2me | Theorems.Thm_lean_workbook_plus_39652
-- name    : lean_workbook_plus_39652
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/15ef3d81-e7b7-4f5d-b5b7-261fb6c875e7
-- statement:
--   Let $t=x+y$ , then the equation is equivalent to: \n $2(x+y)^3+3xy(10-x-y)=2000$ \n $\iff 2(t^2+10t+10^2)(t-10)=3xy(t-10)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39652 {x y t : ℝ} (h₁ : t = x + y) : (2 * (x + y) ^ 3 + 3 * x * y * (10 - x - y) = 2000) ↔ (2 * (t ^ 2 + 10 * t + 10 ^ 2) * (t - 10) = 3 * x * y * (t - 10))   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_4775
-- name    : lean_workbook_plus_4775
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/6a59f6a1-19cc-4285-9571-2d748263bacc
-- statement:
--   Prove that $f(t) = \frac 14( x_1^t + x_2^t + x_3^t + x_4^t); s(t) = \frac 1{81} (x_1^t + x_2^t + x_3^t)(x_2^t + x_3^t + x_4^t)(x_3^t + x_4^t + x_1^t)(x_4^t + x_1^t + x_2^t);$ then $f(4t_1)f(4t_2) \geq s( t_1 + t_2 )$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4775 {x1 x2 x3 x4 : ℝ} (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) (hx4 : 0 < x4) (h : x1 + x2 + x3 + x4 = 1) :  ∀ t1 t2 : ℝ, (1 / 4 * (x1 ^ (4 * t1) + x2 ^ (4 * t1) + x3 ^ (4 * t1) + x4 ^ (4 * t1))) * (1 / 4 * (x1 ^ (4 * t2) + x2 ^ (4 * t2) + x3 ^ (4 * t2) + x4 ^ (4 * t2))) ≥  1 / 81 * (x1 ^ (t1 + t2) + x2 ^ (t1 + t2) + x3 ^ (t1 + t2) + x4 ^ (t1 + t2)) * (x2 ^ (t1 + t2) + x3 ^ (t1 + t2) + x4 ^ (t1 + t2) + x1 ^ (t1 + t2)) * (x3 ^ (t1 + t2) + x4 ^ (t1 + t2) + x1 ^ (t1 + t2) + x2 ^ (t1 + t2)) * (x4 ^ (t1 + t2) + x1 ^ (t1 + t2) + x2 ^ (t1 + t2) + x3 ^ (t1 + t2))   :=  by sorry

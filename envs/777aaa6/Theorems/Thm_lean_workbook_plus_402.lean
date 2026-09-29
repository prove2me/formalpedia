-- Prove2me | Theorems.Thm_lean_workbook_plus_402
-- name    : lean_workbook_plus_402
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/1bdfa73e-f0bf-4427-8eb1-5a0e9e636cfe
-- statement:
--   $ p+q+r=1/a$ \n\n $ pq+qr+pr=b/a$ \n\n $ \rightarrow {ab}=\frac{(pq+qr+pr)}{{(p+q+r)}^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_402  (p q r a b : ℝ)
  (h₀ : p + q + r = 1 / a)
  (h₁ : p * q + q * r + r * p = b / a) :
  a * b = (p * q + q * r + r * p) / (p + q + r)^2   :=  by sorry

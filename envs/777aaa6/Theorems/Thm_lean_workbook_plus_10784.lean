-- Prove2me | Theorems.Thm_lean_workbook_plus_10784
-- name    : lean_workbook_plus_10784
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/cf259b6e-33c2-409f-81e0-afbc7a5e2b5f
-- statement:
--   One way is: $3y=440-4x \implies x(440-4x)=k \implies -4x^2+440x-k=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10784  (x y : ℝ)
  (h₀ : 3 * y = 440 - 4 * x)
  (h₁ : x * (440 - 4 * x) = k) :
  -4 * x^2 + 440 * x - k = 0   :=  by sorry

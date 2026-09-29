-- Prove2me | Theorems.Thm_lean_workbook_plus_17202
-- name    : lean_workbook_plus_17202
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/9a180f7a-a186-44a7-a52b-ba693c60a21d
-- statement:
--   Somehow, using calculus to maximize a quadratic always strikes me as overkill. You could just complete the square. Or use AM-GM: For $ x>0$ and $ 1-x>0,$ $ \sqrt{x(1-x)}\le\frac12(x+(1-x))=\frac12.$ Hence $ x(1-x)\le\frac14,$ with equality when $ x=1-x.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17202  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x < 1) :
  x * (1 - x) ≤ 1 / 4   :=  by sorry

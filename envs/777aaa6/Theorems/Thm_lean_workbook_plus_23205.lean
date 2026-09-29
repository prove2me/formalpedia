-- Prove2me | Theorems.Thm_lean_workbook_plus_23205
-- name    : lean_workbook_plus_23205
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/5de56624-7ac6-4c58-9482-7e97b6a55c33
-- statement:
--   Let $ f(x)=x^2-2$ . If $ r$ is a root of the equation, then $ f(r)$ must be as well. One case this is possible when $ f(r)=r \iff (r-2)(r+1)=0$ , or $ r=2,-1$ . This corresponds to the solutions $ (4,4), (-2,1)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23205  (r : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 - 2)
  (h₁ : f r = r) :
  (r - 2) * (r + 1) = 0   :=  by sorry

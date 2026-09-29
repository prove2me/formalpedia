-- Prove2me | Theorems.Thm_lean_workbook_plus_3904
-- name    : lean_workbook_plus_3904
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/90f881cd-54b3-44c9-ad90-8800935042b7
-- statement:
--   Let $f(a)=a^2(x)+(a+1)^2(y)+(a+2)^2(z)$ .\nWe have $f(1)=305$ , $f(2)=319$ , $f(3)=880$ .\nClearly, $f(a)$ is degree 2.\nWe apply finite differences.\nWe have first differences of $14,561$ and the second difference is $547$ .\n$f(4)=880+561+547=880+1108=\boxed{1988}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3904  (x y z : ℝ)
  (f : ℕ → ℝ)
  (h₀ : ∀ a, f a = a^2 * x + (a + 1)^2 * y + (a + 2)^2 * z)
  (h₁ : f 1 = 305)
  (h₂ : f 2 = 319)
  (h₃ : f 3 = 880) :
  f 4 = 1988   :=  by sorry

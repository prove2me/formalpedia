-- Prove2me | Theorems.Thm_lean_workbook_plus_45482
-- name    : lean_workbook_plus_45482
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/b4315a4e-0f1a-4cb2-bd7c-93217293e104
-- statement:
--   Let $ \frac{m}{n}=a $ . We're given that $ a=\frac{7+\frac{1}{a}}{65-\frac{1}{a}}=\frac{7a+1}{65a-1} $ . Cross-multiplying, we get $ 65a^2-a=7a+1\implies 65a^2-8a-1=0 $ . From the quadratic formula, we have $ a=-\frac{1}{13} $ or $ \frac{1}{5} $ . It's given that $ a $ is positive, so we must have $ a=\frac{1}{5} $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45482  (m n : ℤ)
  (a : ℚ)
  (h₀ : 0 < a)
  (h₁ : 0 < n)
  (h₂ : ¬ 5 * m = 13 * n)
  (h₃ : (m : ℚ) / n = a)
  (h₄ : a = (7 + 1 / a) / (65 - 1 / a)) :
  a = 1 / 5   :=  by sorry

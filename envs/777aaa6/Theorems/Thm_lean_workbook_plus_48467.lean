-- Prove2me | Theorems.Thm_lean_workbook_plus_48467
-- name    : lean_workbook_plus_48467
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/dec0f6bf-39e2-4d17-a55f-011517d8859e
-- statement:
--   if $p, q$ are roots of $ax^2 + bx + c$ with $p > q$ , then $p+q = -b/a$ , $pq = c/a$ , and we are given $p - q = 1$ . Eliminating the variables $p, q$ from this system is easy: We have $ (p+q)^2 - (p-q)^2 = 4pq, $ consequently $ \frac{b^2}{a^2} - 1 = 4\frac{c}{a}, $ and since $a \ne 0$ , the result follows.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48467  (a b c p q : ℝ)
  (h₀ : a ≠ 0)
  (h₁ : a * p^2 + b * p + c = 0)
  (h₂ : a * q^2 + b * q + c = 0)
  (h₃ : p > q)
  (h₄ : p - q = 1) :
  p + q = -b / a ∧ p * q = c / a   :=  by sorry

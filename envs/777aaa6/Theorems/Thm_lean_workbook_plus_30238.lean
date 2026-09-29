-- Prove2me | Theorems.Thm_lean_workbook_plus_30238
-- name    : lean_workbook_plus_30238
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/63ba9a07-8f96-4eaa-a42c-7a42ea8463d3
-- statement:
--   Similarly, $((x+a)(x+b)+c)((x+a)(x+b)+d)=(x^2+108x+2891)(x^2+108x+2907)$ . Comparing the constant terms and subtracting we get $c-d=-16$ . Solving this with $c+d=38$ , we get $c=11$ and $d=27$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30238  (a b c d : ℝ)
  (h₀ : (x + a) * (x + b) + c = x^2 + 108 * x + 2891)
  (h₁ : (x + a) * (x + b) + d = x^2 + 108 * x + 2907)
  (h₂ : c + d = 38)
  (h₃ : c - d = -16) :
  c = 11 ∧ d = 27   :=  by sorry

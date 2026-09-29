-- Prove2me | Theorems.Thm_lean_workbook_plus_31314
-- name    : lean_workbook_plus_31314
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b1b001dc-055c-4a55-a083-bb391a95b0e5
-- statement:
--   Let $a + (k+1)d = b$, then $d = \dfrac{b-a}{k+1}$, which means $ A_t = a + \frac{t}{k+1} (b-a) = \frac{a(k+1-t)}{k+1} + \frac{bt}{k+1}, $ whereas $b = a \vert r \vert^{k+1} \iff \left ( \dfrac{b}{a} \right )^{\frac{1}{k+1}} = \vert r \vert$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31314  (a b r t : ℝ)
  (k : ℕ)
  (h₀ : 0 < k)
  (h₁ : a + (k + 1) * r = b)
  (h₂ : 0 ≤ t)
  (h₃ : t ≤ k + 1) :
  a + t * r = a * (k + 1 - t) / (k + 1) + b * t / (k + 1)   :=  by sorry

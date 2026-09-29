-- Prove2me | Theorems.Thm_lean_workbook_plus_40762
-- name    : lean_workbook_plus_40762
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/1ccf4ccd-1a61-4101-9eb3-00915c23e4e4
-- statement:
--   Note that $ r(x) = f(x) = x^5$ , for $ x = a,b,c,d,e$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40762  (a b c d e : ℝ)
  (f r : ℝ → ℝ)
  (h₀ : ∀ x, r x = f x)
  (h₁ : r a = a^5)
  (h₂ : r b = b^5)
  (h₃ : r c = c^5)
  (h₄ : r d = d^5)
  (h₅ : r e = e^5)
  (h₆ : a ≠ b)
  (h₇ : a ≠ c)
  (h₈ : a ≠ d)
  (h₉ : a ≠ e)
  (h₁₀ : b ≠ c)
  (h₁₁ : b ≠ d)
  (h₁₂ : b ≠ e)
  (h₁₃ : c ≠ d)
  (h₁₄ : c ≠ e)
  (h₁₅ : d ≠ e) :
  r a + r b + r c + r d + r e = a^5 + b^5 + c^5 + d^5 + e^5   :=  by sorry

-- Prove2me | Theorems.Thm_lean_workbook_plus_45335
-- name    : lean_workbook_plus_45335
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/06bd1027-0237-4f3e-b29b-84c8facc9e9b
-- statement:
--   Then $2^{400} = f(\\omega) = A_0 + A_1\\omega + A_2\\omega^2 + A_3\\omega^3 + A_4\\omega^4$ , $2^{400} = f(\\omega^2) = A_0 + A_1\\omega^2 + A_2\\omega^4 + A_3\\omega + A_4\\omega^3$ , $2^{400} = f(\\omega^3) = A_0 + A_1\\omega^3 + A_2\\omega+ A_3\\omega^4 + A_4\\omega^2$ , $2^{400} = f(\\omega^4) = A_0 + A_1\\omega^4 + A_2\\omega^3 + A_3\\omega^2 + A_4\\omega$ , $2^{2000} = f(1) = A_0 + A_1 + A_2 + A_3 + A_4$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45335  (a₀ a₁ a₂ a₃ a₄ : ℝ)
  (f : ℂ → ℂ)
  (h₀ : ∀ z, f z = a₀ + a₁ * z + a₂ * z^2 + a₃ * z^3 + a₄ * z^4)
  (h₁ : f 1 = 2^2000)
  (h₂ : f ω = 2^400)
  (h₃ : f (ω^2) = 2^400)
  (h₄ : f (ω^3) = 2^400)
  (h₅ : f (ω^4) = 2^400) :
  2^2000 = a₀ + a₁ + a₂ + a₃ + a₄   :=  by sorry

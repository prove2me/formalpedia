-- Prove2me | solution 1 for lean_workbook_plus_14025
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:23:13.092752+00:00
-- url     : https://prove2.me/submissions/221f6c27-4090-430c-85d0-1c7759b63f83

import Mathlib.Analysis.Complex.Basic

theorem solution  (a b c p : ℂ)
  (f : ℂ → ℂ)
  (h₀ : ∀ x, f x = x^3 - p * x^2 + (a * b + a * c + b * c) * x - p)
  (h₁ : f a = 0)
  (h₂ : f b = 0)
  (h₃ : f c = 0)
  (h₄ : a ≠ b)
  (h₅ : a ≠ c)
  (h₆ : b ≠ c) :
  ∃ S y, ∀ x, f x = x^3 - S * x^2 + y * x - p :=
  ⟨p, a * b + a * c + b * c, h₀⟩

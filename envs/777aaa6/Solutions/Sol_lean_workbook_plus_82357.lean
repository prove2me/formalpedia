-- Prove2me | solution 1 for lean_workbook_plus_82357
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:06:57.191334+00:00
-- url     : https://prove2.me/submissions/6f3862ab-d5c3-4ede-8959-d48eb2e19e60

import Mathlib

theorem solution (z₁ z₂ z₃ : ℂ)
    (h₀ : z₁^2 + z₂^2 + z₃^2 = z₁ * z₂ + z₂ * z₃ + z₃ * z₁) :
    (z₁ - z₂) * (z₂ - z₃) + (z₂ - z₃) * (z₃ - z₁) +
      (z₃ - z₁) * (z₁ - z₂) = 0 := by
  linear_combination -h₀

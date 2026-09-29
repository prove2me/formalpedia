-- Prove2me | solution 1 for lean_workbook_plus_72479
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:50.161176+00:00
-- url     : https://prove2.me/submissions/1fb301c5-7dc3-49ad-8faa-242f384f3423

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q r s a : ℝ)
  (h₀ : 0 < a)
  (h₁ : r^2 + s^2 = p^2 + q^2)
  (h₂ : (p^2 + 2 * a * p * r + a^2 * r^2) + (q^2 + 2 * a * q * s + a^2 * s^2) = (a^2 * p^2 + 2 * a * p * r + r^2) + (a^2 * q^2 + 2 * a * q * s + s^2)) :
  (p + a * r)^2 + (q + a * s)^2 = (a * p + r)^2 + (a * q + s)^2 := by
  (intros; linarith)

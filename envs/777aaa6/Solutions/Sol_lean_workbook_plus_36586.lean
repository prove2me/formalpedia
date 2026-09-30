-- Prove2me | solution 1 for lean_workbook_plus_36586
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:02:31.128547+00:00
-- url     : https://prove2.me/submissions/e47d8a65-171e-48f6-8ec8-385384a2a50f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (X Y Z W : ℤ) (p s t k : ℤ)
    (h₁ : X = (t^2 + 4 * k * t - 8 * k^2) * p^2 + 2 * (2 * k - t) * p * s - s^2)
    (h₂ : Y = (3 * t^2 - 12 * k * t + 8 * k^2) * p^2 - 2 * (2 * k - t) * p * s + s^2)
    (h₃ : Z = 2 * (2 * k - t)^2 * p^2 - 2 * (2 * k - t) * p * s)
    (h₄ : W = t^2 * p^2 + 2 * (2 * k - t) * p * s - s^2) :
    X^2 + Y^2 = 2 * Z^2 + 2 * W^2 := by
  rw [h₁, h₂, h₃, h₄]
  ring

#print axioms solution

-- Prove2me | solution 1 for SteinENT.two_squares_composition
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:26:46.786413+00:00
-- url     : https://prove2.me/submissions/26a2aeac-1e9a-4aab-94af-1dbf9e82bdf1

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace SteinENT

theorem _root_.solution (x₁ y₁ x₂ y₂ : ℤ) :
    (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2) =
      (x₁ * x₂ - y₁ * y₂) ^ 2 + (x₁ * y₂ + x₂ * y₁) ^ 2 := by
  ring

end SteinENT

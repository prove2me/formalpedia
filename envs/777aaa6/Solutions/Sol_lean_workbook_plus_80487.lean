-- Prove2me | solution 1 for lean_workbook_plus_80487
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:33:53.582122+00:00
-- url     : https://prove2.me/submissions/a599fd8a-0501-4a9e-ac3f-78a8d1fe754c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (x y z : ℂ) (h₀ : 2 * z^2 = 3 * (x * y))
    (h₁ : x^3 + y^3 + z^3 = x^3 + y^3 + (-z)^3 - 3 * (x * y) * (-z)) :
    x^3 + y^3 + z^3 = (x + y - z) * (x^2 + z * x - x * y + z * y + z^2 + y^2) := by
  calc
    _ = x^3 + y^3 + (-z)^3 - 3 * (x * y) * (-z) := h₁
    _ = _ := by ring

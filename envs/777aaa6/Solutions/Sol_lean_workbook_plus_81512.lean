-- Prove2me | solution 1 for lean_workbook_plus_81512
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:35:17.157296+00:00
-- url     : https://prove2.me/submissions/f3469e2d-8771-4a52-a464-0d9a39923888

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Ring

theorem solution (x y : ℤ) :
    (x - y) ^ 2 ∣ x ^ 2 + y ^ 2 → (x - y) ^ 2 ∣ 2 * x * y := by
  intro h
  convert dvd_sub h (dvd_refl ((x - y) ^ 2)) using 1 <;> ring

#print axioms solution

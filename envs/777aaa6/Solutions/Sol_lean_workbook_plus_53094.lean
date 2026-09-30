-- Prove2me | solution 1 for lean_workbook_plus_53094
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:39:01.453477+00:00
-- url     : https://prove2.me/submissions/6bc5a9a9-ffb8-4a1a-834f-fb8757bed4dc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum

theorem solution (n : ℕ) :
    n % 2 = 1 → 5 ∣ 1 ^ n + 4 ^ n ∧ 5 ∣ 2 ^ n + 3 ^ n := by
  intro hn
  have ho : Odd n := ⟨n / 2, by omega⟩
  constructor
  · simpa using ho.nat_add_dvd_pow_add_pow (x := 1) (y := 4)
  · simpa using ho.nat_add_dvd_pow_add_pow (x := 2) (y := 3)

#print axioms solution

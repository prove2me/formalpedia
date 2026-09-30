-- Prove2me | solution 1 for lean_workbook_plus_81010
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:47:44.910176+00:00
-- url     : https://prove2.me/submissions/de4ec86b-e581-4d1d-9677-0709c7981d69

import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq

theorem solution {a m : ℤ} (h : a.gcd m = 1) :
    ∃ x, a * x ≡ 1 [ZMOD m] := by
  refine ⟨Int.gcdA a m, Int.modEq_iff_dvd.mpr ⟨Int.gcdB a m, ?_⟩⟩
  have hbezout : (1 : ℤ) = a * Int.gcdA a m + m * Int.gcdB a m := by
    simpa only [h, Int.natCast_one] using Int.gcd_eq_gcd_ab a m
  rw [hbezout, add_sub_cancel_left]

#print axioms solution

-- Prove2me | solution 1 for lean_workbook_plus_39039
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:03:58.867665+00:00
-- url     : https://prove2.me/submissions/17b7c321-2915-4319-a6e8-472b93f1e86a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Ring.Parity

theorem solution (k : ℕ) (h : k % 2 = 1) :
    (k + 3).choose 2 * (-1 : ℤ) ^ (k + 1) +
      (k + 2).choose 2 * (-1) ^ k = (k + 2) := by
  have hk : Odd k := Nat.odd_iff.mpr h
  have he : Even (k + 1) := hk.add_odd (by decide : Odd 1)
  have hc : (k + 3).choose 2 = k + 2 + (k + 2).choose 2 := by
    simpa [Nat.add_assoc] using Nat.choose_succ_succ (k + 2) 1
  rw [he.neg_one_pow, hk.neg_one_pow]
  simp [hc, Nat.cast_add]

#print axioms solution

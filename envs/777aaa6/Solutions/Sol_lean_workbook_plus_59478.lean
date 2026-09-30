-- Prove2me | solution 1 for lean_workbook_plus_59478
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:20:20.536981+00:00
-- url     : https://prove2.me/submissions/124134a3-1675-4145-b5fc-d8a8cd6bc775

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

namespace SixModuloFortyNine

theorem closed_form (n : ℕ) :
    (6 : ZMod 49) ^ n = (-1) ^ n * (1 - 7 * (n : ZMod 49)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (6 : ZMod 49) ^ (n + 1) = (-1) ^ n * (1 - 7 * (n : ZMod 49)) * 6 := by
        rw [pow_succ, ih]
      _ = (-1) ^ (n + 1) * (1 - 7 * ((n + 1 : ℕ) : ZMod 49)) -
          49 * ((-1) ^ n) * (n : ZMod 49) := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        ring
      _ = (-1) ^ (n + 1) * (1 - 7 * ((n + 1 : ℕ) : ZMod 49)) := by
        have hz : (49 : ZMod 49) = 0 := by decide
        rw [hz]
        ring

theorem period : (6 : ZMod 49) ^ 14 = 1 := by
  rw [closed_form]
  decide

theorem residue_classification (n : ℕ) :
    (6 : ZMod 49) ^ n = 6 ↔ n % 14 = 1 := by
  rw [pow_eq_pow_mod n period]
  have hlt := Nat.mod_lt n (by decide : 0 < 14)
  generalize n % 14 = r at *
  interval_cases r <;> decide

theorem integer_classification (n : ℕ) :
    (6 : ℤ) ^ n ≡ 6 [ZMOD 49] ↔ n % 14 = 1 := by
  have hc : ((6 : ZMod 49) ^ n = 6) ↔ (6 : ℤ) ^ n ≡ 6 [ZMOD 49] := by
    simpa only [Int.cast_pow, Int.cast_ofNat, Nat.cast_ofNat] using
      (ZMod.intCast_eq_intCast_iff ((6 : ℤ) ^ n) 6 49)
  exact hc.symm.trans (residue_classification n)

end SixModuloFortyNine

theorem solution : 6 ^ 2003 ≡ 6 [ZMOD 49] :=
  (SixModuloFortyNine.integer_classification 2003).mpr (by decide)

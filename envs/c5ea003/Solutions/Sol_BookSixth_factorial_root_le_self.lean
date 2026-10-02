-- Prove2me | solution 1 for BookSixth.factorial_root_le_self
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T06:36:23.690623+00:00
-- url     : https://prove2.me/submissions/4e83a4c0-31a0-429a-afda-aa7a0f529ae5

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (r : Nat) (hr : 0 < r) :
    ((r.factorial : Real)) ^ ((1 : Real) / (r : Real)) ≤ (r : Real) := by
  have hfact : (r.factorial : Real) ≤ (r : Real) ^ r := by
    clear hr
    induction r with
    | zero => simp
    | succ k ih =>
      have hk : (0 : Real) ≤ (k : Real) := Nat.cast_nonneg k
      have hkp : (k : Real) ≤ (((k + 1 : Nat)) : Real) :=
        Nat.cast_le.mpr (Nat.le_succ k)
      have hmon : (k : Real) ^ k ≤ (((k + 1 : Nat)) : Real) ^ k :=
        pow_le_pow_left₀ hk hkp k
      have ih' : (k.factorial : Real) ≤ (((k + 1 : Nat)) : Real) ^ k :=
        ih.trans hmon
      have hnn : (0 : Real) ≤ (((k + 1 : Nat)) : Real) := by positivity
      have hstep : (((k + 1 : Nat)) : Real) * (k.factorial : Real)
          ≤ (((k + 1 : Nat)) : Real) * ((((k + 1 : Nat)) : Real) ^ k) :=
        mul_le_mul_of_nonneg_left ih' hnn
      have hfact : ((((k + 1 : Nat).factorial : Nat)) : Real)
          = (((k + 1 : Nat)) : Real) * (k.factorial : Real) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      have hpow : ((((k + 1 : Nat))) : Real) ^ (k + 1)
          = (((k + 1 : Nat)) : Real) * ((((k + 1 : Nat)) : Real) ^ k) := by
        rw [pow_succ]; ring
      rw [hfact, hpow]
      exact hstep
  have hrR : (0 : Real) < (r : Real) := Nat.cast_pos.mpr hr
  have hexp : (0 : Real) ≤ (1 : Real) / (r : Real) := by positivity
  have hbase : (0 : Real) ≤ (r.factorial : Real) := by positivity
  calc ((r.factorial : Real)) ^ ((1 : Real) / (r : Real))
      ≤ (((r : Real) ^ r)) ^ ((1 : Real) / (r : Real)) :=
        Real.rpow_le_rpow hbase hfact hexp
    _ = (r : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hrR)]
        have hcancel : (r : Real) * ((1 : Real) / (r : Real)) = 1 :=
          mul_one_div_cancel (ne_of_gt hrR)
        rw [hcancel, Real.rpow_one]

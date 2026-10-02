-- Prove2me | solution 1 for BookSixth.factorial_le_self_pow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T06:28:40.214028+00:00
-- url     : https://prove2.me/submissions/b873e316-522e-4852-b3ef-2be43c1649f0

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : Nat) : (n.factorial : Real) ≤ (n : Real) ^ n := by
  induction n with
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

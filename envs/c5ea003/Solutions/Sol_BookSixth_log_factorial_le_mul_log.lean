-- Prove2me | solution 1 for BookSixth.log_factorial_le_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T06:45:23.825976+00:00
-- url     : https://prove2.me/submissions/86cf561d-4f4a-4d8f-93b9-9daa6dacaaba

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (r : Nat) :
    Real.log (r.factorial : Real) ≤ (r : Real) * Real.log (r : Real) := by
  have hfact : (r.factorial : Real) ≤ (r : Real) ^ r := by
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
      have hfeq : ((((k + 1 : Nat).factorial : Nat)) : Real)
          = (((k + 1 : Nat)) : Real) * (k.factorial : Real) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      have hpow : ((((k + 1 : Nat))) : Real) ^ (k + 1)
          = (((k + 1 : Nat)) : Real) * ((((k + 1 : Nat)) : Real) ^ k) := by
        rw [pow_succ]; ring
      rw [hfeq, hpow]
      exact hstep
  have hpos : (0 : Real) < (r.factorial : Real) := by
    apply Nat.cast_pos.mpr (Nat.factorial_pos r)
  have hlog := Real.log_le_log hpos hfact
  rw [Real.log_pow] at hlog
  exact hlog

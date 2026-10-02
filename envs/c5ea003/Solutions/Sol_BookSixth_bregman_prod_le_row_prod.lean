-- Prove2me | solution 1 for BookSixth.bregman_prod_le_row_prod
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T06:40:01.867081+00:00
-- url     : https://prove2.me/submissions/3b8f811a-ac54-4a8f-8a8e-3979d14153ea

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : Nat) (r : Fin n → Nat) (hpos : ∀ i, 0 < r i) :
    ∏ i, ((r i).factorial : Real) ^ ((1 : Real) / (r i : Real))
      ≤ ∏ i, (r i : Real) := by
  have hfact : ∀ m : Nat, (m.factorial : Real) ≤ (m : Real) ^ m := by
    intro m
    induction m with
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
  apply Finset.prod_le_prod
  · intro i _
    apply Real.rpow_nonneg
    positivity
  · intro i _
    have hrR : (0 : Real) < ((r i : Nat) : Real) := Nat.cast_pos.mpr (hpos i)
    have hexp : (0 : Real) ≤ (1 : Real) / (((r i : Nat)) : Real) := by positivity
    have hbase : (0 : Real) ≤ (((r i).factorial : Nat) : Real) := by positivity
    calc ((((r i).factorial : Nat)) : Real) ^ ((1 : Real) / (((r i : Nat)) : Real))
        ≤ (((((r i : Nat))) : Real) ^ (r i)) ^ ((1 : Real) / (((r i : Nat)) : Real)) :=
          Real.rpow_le_rpow hbase (hfact (r i)) hexp
      _ = ((((r i : Nat))) : Real) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hrR)]
          have hcancel : ((((r i : Nat))) : Real) * ((1 : Real) / ((((r i : Nat))) : Real)) = 1 :=
            mul_one_div_cancel (ne_of_gt hrR)
          rw [hcancel, Real.rpow_one]

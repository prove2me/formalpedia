-- Prove2me | solution 1 for mme_surplus_arith_four
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-22T21:37:31.521234+00:00
-- url     : https://prove2.me/submissions/3cd3e99e-a802-43aa-9ea2-08747f9f5d15

import Mathlib

set_option autoImplicit false

theorem solution : forall copies abc : Nat, 1 <= copies -> 390625 <= abc -> (((7 ^ 4 : Nat)) : Real) < (copies : Real) * ((((abc : Nat)) : Real) ^ (((3952233 : Real)) / 5000000)) := by
  intro copies abc hcopies habc
  have h74 : (((7 ^ 4 : Nat)) : Real) = 2401 := by norm_num
  have hE : (((6 : Nat)) : Real) < (((8 : Nat)) : Real) * (((3952233 : Real)) / 5000000) := by norm_num
  have hmono : (5 : Real) ^ ((((6 : Nat)) : Real)) < (5 : Real) ^ ((((8 : Nat)) : Real) * (((3952233 : Real)) / 5000000)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hE
  have h56 : (5 : Real) ^ ((((6 : Nat)) : Real)) = 15625 := by
    rw [Real.rpow_natCast]
    norm_num
  have h05 : (0 : Real) ≤ 5 := by norm_num
  have h5Y : (5 : Real) ^ ((((8 : Nat)) : Real)) = ((((390625 : Nat))) : Real) := by
    rw [Real.rpow_natCast]
    norm_num
  have ejoin : (5 : Real) ^ ((((8 : Nat)) : Real) * (((3952233 : Real)) / 5000000)) = ((((390625 : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) := by
    rw [Real.rpow_mul h05, h5Y]
  have hbase : ((((390625 : Nat))) : Real) ≤ ((((abc : Nat))) : Real) := by
    exact_mod_cast habc
  have hmono2 : ((((390625 : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) ≤ ((((abc : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) :=
    Real.rpow_le_rpow (by positivity) hbase (by positivity)
  have hcop : (1 : Real) ≤ (copies : Real) := by
    exact_mod_cast hcopies
  have hnn2 : (0 : Real) ≤ ((((abc : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) :=
    Real.rpow_nonneg (by positivity) _
  have hmul : ((((abc : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) ≤ (copies : Real) * ((((abc : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) :=
    le_mul_of_one_le_left hnn2 hcop
  calc (((7 ^ 4 : Nat)) : Real) = (2401 : Real) := h74
    _ < 15625 := by norm_num
    _ = (5 : Real) ^ ((((6 : Nat)) : Real)) := h56.symm
    _ < (5 : Real) ^ ((((8 : Nat)) : Real) * (((3952233 : Real)) / 5000000)) := hmono
    _ = ((((390625 : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) := ejoin
    _ ≤ ((((abc : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) := hmono2
    _ ≤ (copies : Real) * ((((abc : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) := hmul

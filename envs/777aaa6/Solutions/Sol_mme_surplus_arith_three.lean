-- Prove2me | solution 1 for mme_surplus_arith_three
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-22T20:31:46.349893+00:00
-- url     : https://prove2.me/submissions/6174bef4-fe46-4d64-b1d7-d1989e19f0ee

import Mathlib

set_option autoImplicit false

theorem solution : forall copies abc : Nat, 1 <= copies -> 15625 <= abc -> (((7 ^ 3 : Nat)) : Real) < (copies : Real) * ((((abc : Nat)) : Real) ^ (((3952233 : Real)) / 5000000)) := by
  intro copies abc hcopies habc
  have h73 : (((7 ^ 3 : Nat)) : Real) = 343 := by norm_num
  have hE : (((4 : Nat)) : Real) < (((6 : Nat)) : Real) * (((3952233 : Real)) / 5000000) := by norm_num
  have hmono : (5 : Real) ^ ((((4 : Nat)) : Real)) < (5 : Real) ^ ((((6 : Nat)) : Real) * (((3952233 : Real)) / 5000000)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hE
  have h54 : (5 : Real) ^ ((((4 : Nat)) : Real)) = 625 := by
    rw [Real.rpow_natCast]
    norm_num
  have h05 : (0 : Real) ≤ 5 := by norm_num
  have h5Y : (5 : Real) ^ ((((6 : Nat)) : Real)) = ((((15625 : Nat))) : Real) := by
    rw [Real.rpow_natCast]
    norm_num
  have ejoin : (5 : Real) ^ ((((6 : Nat)) : Real) * (((3952233 : Real)) / 5000000)) = ((((15625 : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) := by
    rw [Real.rpow_mul h05, h5Y]
  have hbase : ((((15625 : Nat))) : Real) ≤ ((((abc : Nat))) : Real) := by
    exact_mod_cast habc
  have hmono2 : ((((15625 : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) ≤ ((((abc : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) :=
    Real.rpow_le_rpow (by positivity) hbase (by positivity)
  have hcop : (1 : Real) ≤ (copies : Real) := by
    exact_mod_cast hcopies
  have hnn2 : (0 : Real) ≤ ((((abc : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) :=
    Real.rpow_nonneg (by positivity) _
  have hmul : ((((abc : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) ≤ (copies : Real) * ((((abc : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) :=
    le_mul_of_one_le_left hnn2 hcop
  calc (((7 ^ 3 : Nat)) : Real) = (343 : Real) := h73
    _ < 625 := by norm_num
    _ = (5 : Real) ^ ((((4 : Nat)) : Real)) := h54.symm
    _ < (5 : Real) ^ ((((6 : Nat)) : Real) * (((3952233 : Real)) / 5000000)) := hmono
    _ = ((((15625 : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) := ejoin
    _ ≤ ((((abc : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) := hmono2
    _ ≤ (copies : Real) * ((((abc : Nat))) : Real) ^ (((3952233 : Real)) / 5000000) := hmul

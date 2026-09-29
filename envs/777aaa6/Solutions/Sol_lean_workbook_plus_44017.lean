-- Prove2me | solution 1 for lean_workbook_plus_44017
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:48:08.36296+00:00
-- url     : https://prove2.me/submissions/7b939187-2dca-4894-81ca-b7b4a858e5a1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : 2003 ^ ((2002 ^ 2001) % 10000) ≡ 241 [MOD 1000] := by
  have base1 : (2003 : ℕ)^1 ≡ 3 [MOD 1000] := by norm_num [Nat.ModEq]
  have base3 : (2003 : ℕ)^3 ≡ 27 [MOD 1000] := by
    rw [show 3 = 1*2+1 by decide,pow_add,pow_mul]
    exact ((base1.pow 2).mul base1).trans (by norm_num [Nat.ModEq])
  have base6 : (2003 : ℕ)^6 ≡ 729 [MOD 1000] := by
    rw [show 6 = 3*2 by decide,pow_mul]
    exact (base3.pow 2).trans (by norm_num [Nat.ModEq])
  have base12 : (2003 : ℕ)^12 ≡ 441 [MOD 1000] := by
    rw [show 12 = 6*2 by decide,pow_mul]
    exact (base6.pow 2).trans (by norm_num [Nat.ModEq])
  have base25 : (2003 : ℕ)^25 ≡ 443 [MOD 1000] := by
    rw [show 25 = 12*2+1 by decide,pow_add,pow_mul]
    exact ((base12.pow 2).mul base1).trans (by norm_num [Nat.ModEq])
  have base50 : (2003 : ℕ)^50 ≡ 249 [MOD 1000] := by
    rw [show 50 = 25*2 by decide,pow_mul]
    exact (base25.pow 2).trans (by norm_num [Nat.ModEq])
  have base100 : (2003 : ℕ)^100 ≡ 1 [MOD 1000] := by
    rw [show 100 = 50*2 by decide,pow_mul]
    exact (base50.pow 2).trans (by norm_num [Nat.ModEq])
  have exp1 : (2002 : ℕ)^1 ≡ 2 [MOD 100] := by norm_num [Nat.ModEq]
  have exp3 : (2002 : ℕ)^3 ≡ 8 [MOD 100] := by
    rw [show 3 = 1*2+1 by decide,pow_add,pow_mul]
    exact ((exp1.pow 2).mul exp1).trans (by norm_num [Nat.ModEq])
  have exp7 : (2002 : ℕ)^7 ≡ 28 [MOD 100] := by
    rw [show 7 = 3*2+1 by decide,pow_add,pow_mul]
    exact ((exp3.pow 2).mul exp1).trans (by norm_num [Nat.ModEq])
  have exp15 : (2002 : ℕ)^15 ≡ 68 [MOD 100] := by
    rw [show 15 = 7*2+1 by decide,pow_add,pow_mul]
    exact ((exp7.pow 2).mul exp1).trans (by norm_num [Nat.ModEq])
  have exp31 : (2002 : ℕ)^31 ≡ 48 [MOD 100] := by
    rw [show 31 = 15*2+1 by decide,pow_add,pow_mul]
    exact ((exp15.pow 2).mul exp1).trans (by norm_num [Nat.ModEq])
  have exp62 : (2002 : ℕ)^62 ≡ 4 [MOD 100] := by
    rw [show 62 = 31*2 by decide,pow_mul]
    exact (exp31.pow 2).trans (by norm_num [Nat.ModEq])
  have exp125 : (2002 : ℕ)^125 ≡ 32 [MOD 100] := by
    rw [show 125 = 62*2+1 by decide,pow_add,pow_mul]
    exact ((exp62.pow 2).mul exp1).trans (by norm_num [Nat.ModEq])
  have exp250 : (2002 : ℕ)^250 ≡ 24 [MOD 100] := by
    rw [show 250 = 125*2 by decide,pow_mul]
    exact (exp125.pow 2).trans (by norm_num [Nat.ModEq])
  have exp500 : (2002 : ℕ)^500 ≡ 76 [MOD 100] := by
    rw [show 500 = 250*2 by decide,pow_mul]
    exact (exp250.pow 2).trans (by norm_num [Nat.ModEq])
  have exp1000 : (2002 : ℕ)^1000 ≡ 76 [MOD 100] := by
    rw [show 1000 = 500*2 by decide,pow_mul]
    exact (exp500.pow 2).trans (by norm_num [Nat.ModEq])
  have exp2001 : (2002 : ℕ)^2001 ≡ 52 [MOD 100] := by
    rw [show 2001 = 1000*2+1 by decide,pow_add,pow_mul]
    exact ((exp1000.pow 2).mul exp1).trans (by norm_num [Nat.ModEq])
  have val1 : (2003 : ℕ)^1 ≡ 3 [MOD 1000] := by norm_num [Nat.ModEq]
  have val3 : (2003 : ℕ)^3 ≡ 27 [MOD 1000] := by
    rw [show 3 = 1*2+1 by decide,pow_add,pow_mul]
    exact ((val1.pow 2).mul val1).trans (by norm_num [Nat.ModEq])
  have val6 : (2003 : ℕ)^6 ≡ 729 [MOD 1000] := by
    rw [show 6 = 3*2 by decide,pow_mul]
    exact (val3.pow 2).trans (by norm_num [Nat.ModEq])
  have val13 : (2003 : ℕ)^13 ≡ 323 [MOD 1000] := by
    rw [show 13 = 6*2+1 by decide,pow_add,pow_mul]
    exact ((val6.pow 2).mul val1).trans (by norm_num [Nat.ModEq])
  have val26 : (2003 : ℕ)^26 ≡ 329 [MOD 1000] := by
    rw [show 26 = 13*2 by decide,pow_mul]
    exact (val13.pow 2).trans (by norm_num [Nat.ModEq])
  have val52 : (2003 : ℕ)^52 ≡ 241 [MOD 1000] := by
    rw [show 52 = 26*2 by decide,pow_mul]
    exact (val26.pow 2).trans (by norm_num [Nat.ModEq])
  have reduce (e : ℕ) : 2003^e ≡ 2003^(e%100) [MOD 1000] := by
    conv_lhs => rw [← Nat.mod_add_div e 100]
    rw [pow_add,pow_mul]
    simpa only [one_pow,mul_one] using (Nat.ModEq.refl (2003^(e%100))).mul (base100.pow (e/100))
  have hE : (2002^2001)%100 = 52 := exp2001
  have sourceClaim : 2003^(2002^2001) ≡ 241 [MOD 1000] := by
    have h := reduce (2002^2001)
    rw [hE] at h
    exact h.trans val52
  have hB := reduce ((2002^2001)%10000)
  rw [Nat.mod_mod_of_dvd _ (by decide : 100 ∣ 10000),hE] at hB
  have hS := reduce (2002^2001)
  rw [hE] at hS
  exact (hB.trans hS.symm).trans sourceClaim

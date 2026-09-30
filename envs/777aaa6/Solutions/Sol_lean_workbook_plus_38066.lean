-- Prove2me | solution 1 for lean_workbook_plus_38066
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:34:15.351261+00:00
-- url     : https://prove2.me/submissions/fba4b44f-3d3c-426d-b47e-27c74710edfa

import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

theorem prime_binomial_row (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : k < p) :
    ((p - 1).choose k : ZMod p) = (-1) ^ k := by
  revert hk
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hzero : (p.choose (k + 1) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (hp.dvd_choose_self (by omega) hk)
      have hpascal := congrArg (fun n : ℕ => (n : ZMod p))
        (Nat.choose_succ_succ (p - 1) k)
      simp only [Nat.succ_eq_add_one] at hpascal
      rw [Nat.sub_add_cancel hp.one_le, Nat.cast_add, hzero, hprev] at hpascal
      have hnext : ((p - 1).choose (k + 1) : ZMod p) = -((-1 : ZMod p) ^ k) := by
        apply add_left_cancel (a := (-1 : ZMod p) ^ k)
        simpa using hpascal.symm
      simpa [pow_succ] using hnext

theorem prime_binomial_row_int (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : k < p) :
    ((p - 1).choose k : ℤ) ≡ (-1 : ℤ) ^ k [ZMOD p] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  simpa only [Int.cast_natCast, Int.cast_pow, Int.cast_neg, Int.cast_one] using
    prime_binomial_row p hp k hk

theorem prime_central_binomial_congruence (p : ℕ) (hp : p.Prime) :
    ((p - 1).choose ((p - 1) / 2) : ℤ) ≡ (-1 : ℤ) ^ ((p - 1) / 2) [ZMOD p] := by
  apply prime_binomial_row_int p hp
  have := hp.two_le
  omega

theorem solution (p : ℕ) (_hp : p.Prime) (hpo : Odd p) :
    ((p - 1).choose (p - 1) / 2) ≡ (-1 : ℤ) ^ (p - 1) / 2 [ZMOD p] := by
  have heven : Even (p - 1) := Nat.even_iff.mpr (by
    have := Nat.odd_iff.mp hpo
    omega)
  norm_num [heven.neg_one_pow]

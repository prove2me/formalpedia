-- Prove2me | solution 1 for lean_workbook_plus_66435
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:21:09.612506+00:00
-- url     : https://prove2.me/submissions/3de72562-b030-4c47-a7c7-db65d58c373b

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

private lemma period_twenty_four (n : ℕ) :
    200 ^ n % 1489 = 200 ^ (n % 24) % 1489 := by
  conv_lhs => rw [← Nat.mod_add_div n 24]
  rw [pow_add, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

private lemma forced_residue (n : ℕ) (hc : Nat.ModEq 1489 3 (2 ^ n)) :
    n % 24 = 13 := by
  have hp : 200 ^ n % 1489 = 1289 := by
    have h := (hc.pow 31).symm
    change (2 ^ n) ^ 31 % 1489 = 3 ^ 31 % 1489 at h
    rw [← pow_mul, Nat.mul_comm n 31, pow_mul] at h
    norm_num [Nat.pow_mod] at h
    exact h
  have hr := period_twenty_four n
  rw [hp] at hr
  have hlt := Nat.mod_lt n (by decide : 0 < 24)
  have unique_residue : ∀ r : Fin 24, 200 ^ r.val % 1489 = 1289 → r.val = 13 := by
    decide
  exact unique_residue ⟨n % 24, hlt⟩ hr.symm

theorem positive_case (n : ℕ) (hn : 0 < n) (hdiv : n ∣ 2 ^ n - 3) :
    ¬ 1489 ∣ n := by
  intro hd
  have hbig : 1489 ≤ n := Nat.le_of_dvd hn hd
  have hle : 3 ≤ 2 ^ n := by
    have hpow : 2 ^ 2 ≤ 2 ^ n := pow_le_pow_right₀ (by decide) (by omega)
    omega
  have hc : Nat.ModEq n 3 (2 ^ n) := (Nat.modEq_iff_dvd' hle).mpr hdiv
  have hr : n % 24 = 13 :=
    forced_residue n ((Nat.modEq_iff_dvd' hle).mpr (hd.trans hdiv))
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hj : jacobiSym (6 : ℤ) n = -1 := by
    rw [jacobiSym.mod_right 6 hodd]
    norm_num [hr]
  have hz : (2 : ZMod n) ^ n = 3 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (ZMod.natCast_eq_natCast_iff (2 ^ n) 3 n).mpr hc.symm
  have hsquare : IsSquare (6 : ZMod n) := by
    obtain ⟨k, hk⟩ := hodd
    refine ⟨(2 : ZMod n) ^ (k + 1), ?_⟩
    rw [← pow_add, show k + 1 + (k + 1) = n + 1 by omega, pow_succ, hz]
    norm_num
  exact ZMod.nonsquare_of_jacobiSym_eq_neg_one hj (by simpa using hsquare)

theorem corrected_statement (n : ℕ) (hdiv : n ∣ 2 ^ n - 3) :
    (1489 ∣ n) ↔ n = 0 := by
  constructor
  · intro hd
    by_contra hn
    exact positive_case n (Nat.pos_of_ne_zero hn) hdiv hd
  · rintro rfl
    exact dvd_zero _

theorem solution : ¬ (∀ n : ℕ, n ∣ (2 ^ n - 3) → ¬ 1489 ∣ n) := by
  intro h
  exact h 0 (by norm_num) (by norm_num)

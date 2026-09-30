-- Prove2me | solution 1 for lean_workbook_plus_15389
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:28:55.814649+00:00
-- url     : https://prove2.me/submissions/4bb3fac9-0fe2-4c81-82da-b967be1f2b43

import Mathlib.NumberTheory.FLT.Three
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.GCD


theorem solution (p q r : ℚ) (hp : p + q + r = 0) (hq : p * q * r = 1) : False := by
  have hr : r = -(p + q) := by linarith
  subst hr
  have key : p * q * (p + q) = -1 := by linarith [hq]
  have hp0 : p ≠ 0 := by rintro rfl; simp at hq
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hpq0 : p + q ≠ 0 := by intro h; rw [h] at hq; simp at hq
  -- pass to integers
  set a : ℤ := p.num * q.den with ha
  set b : ℤ := q.num * p.den with hb
  set d : ℤ := (p.den : ℤ) * q.den with hd
  have hd0 : d ≠ 0 := by positivity
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  have haQ : (a : ℚ) = p * d := by
    simp only [ha, hd]; push_cast
    rw [← Rat.mul_den_eq_num p]; ring
  have hbQ : (b : ℚ) = q * d := by
    simp only [hb, hd]; push_cast
    rw [← Rat.mul_den_eq_num q]; ring
  have hab : a * b * (a + b) = (-d) ^ 3 := by
    have : ((a * b * (a + b) : ℤ) : ℚ) = (((-d) ^ 3 : ℤ) : ℚ) := by
      push_cast
      rw [haQ, hbQ]
      linear_combination (d : ℚ) ^ 3 * key
    exact_mod_cast this
  have ha0 : a ≠ 0 := by
    intro h
    have : (a : ℚ) = 0 := by exact_mod_cast h
    rw [haQ] at this
    exact mul_ne_zero hp0 hdQ this
  have hb0 : b ≠ 0 := by
    intro h
    have : (b : ℚ) = 0 := by exact_mod_cast h
    rw [hbQ] at this
    exact mul_ne_zero hq0 hdQ this
  have hab0 : a + b ≠ 0 := by
    intro h
    have : ((a + b : ℤ) : ℚ) = 0 := by exact_mod_cast h
    push_cast at this
    rw [haQ, hbQ, ← add_mul] at this
    exact mul_ne_zero hpq0 hdQ this
  -- divide out the gcd
  have hgpos : 0 < Int.gcd a b := Int.gcd_pos_of_ne_zero_left b ha0
  obtain ⟨a', b', hcop, ha', hb'⟩ := Int.exists_gcd_one hgpos
  set g : ℤ := (Int.gcd a b : ℤ) with hg
  have hg0 : g ≠ 0 := by positivity
  have hg3 : g ^ 3 * (a' * b' * (a' + b')) = (-d) ^ 3 := by
    rw [ha', hb'] at hab; linear_combination hab
  have hgd : g ∣ d := by
    have h1 : g ^ 3 ∣ d ^ 3 := by
      refine ⟨-(a' * b' * (a' + b')), ?_⟩
      linear_combination hg3
    exact (Int.pow_dvd_pow_iff (by norm_num)).mp h1
  obtain ⟨d', hd'⟩ := hgd
  have hmain : a' * b' * (a' + b') = (-d') ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hg0)
    rw [hg3, hd']; ring
  have hcop' : IsCoprime a' b' := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hcop1 : IsCoprime a' (a' + b') := by
    obtain ⟨u, v, huv⟩ := hcop'
    exact ⟨u - v, v, by linear_combination huv⟩
  have hcop2 : IsCoprime b' (a' + b') := by
    obtain ⟨u, v, huv⟩ := hcop'
    exact ⟨v - u, u, by linear_combination huv⟩
  -- each factor is a cube
  obtain ⟨u, hu⟩ := Int.eq_pow_of_mul_eq_pow_odd_left (hcop'.mul_right hcop1) (by decide : Odd 3)
    (show a' * (b' * (a' + b')) = (-d') ^ 3 by rw [← hmain]; ring)
  obtain ⟨v, hv⟩ := Int.eq_pow_of_mul_eq_pow_odd_left (hcop'.symm.mul_right hcop2) (by decide : Odd 3)
    (show b' * (a' * (a' + b')) = (-d') ^ 3 by rw [← hmain]; ring)
  obtain ⟨w, hw⟩ := Int.eq_pow_of_mul_eq_pow_odd_left (hcop1.symm.mul_right hcop2.symm) (by decide : Odd 3)
    (show (a' + b') * (a' * b') = (-d') ^ 3 by rw [← hmain]; ring)
  -- nonvanishing
  have ha'0 : a' ≠ 0 := by rintro rfl; simp at ha'; exact ha0 ha'
  have hb'0 : b' ≠ 0 := by rintro rfl; simp at hb'; exact hb0 hb'
  have hab'0 : a' + b' ≠ 0 := by
    intro h
    apply hab0
    rw [ha', hb', ← add_mul, h, zero_mul]
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu; exact ha'0 hu
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv; exact hb'0 hv
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; exact hab'0 hw
  -- Fermat's last theorem for exponent 3
  have flt : FermatLastTheoremWith ℤ 3 := fermatLastTheoremFor_iff_int.mp fermatLastTheoremThree
  exact flt u v w hu0 hv0 hw0 (by rw [← hu, ← hv, ← hw])

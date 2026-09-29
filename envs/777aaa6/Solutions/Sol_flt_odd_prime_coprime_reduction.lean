-- Prove2me | solution 1 for flt_odd_prime_coprime_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-11T18:30:16.649817+00:00
-- url     : https://prove2.me/submissions/d4f6acd4-40bf-42d3-a58b-367eed0d0015

import Theorems.Thm_flt_odd_prime_coprime_reduction
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem solution
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcoprime : ∀ (a' b' c' : ℕ), 0 < a' → 0 < b' → 0 < c' →
      Nat.Coprime a' b' → Nat.Coprime b' c' → Nat.Coprime a' c' →
      a' ^ p + b' ^ p ≠ c' ^ p) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  set d := Nat.gcd a b with hd_def
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left b ha
  have hda : d ∣ a := Nat.gcd_dvd_left a b
  have hdb : d ∣ b := Nat.gcd_dvd_right a b
  have hdap : d ^ p ∣ a ^ p := pow_dvd_pow_of_dvd hda p
  have hdbp : d ^ p ∣ b ^ p := pow_dvd_pow_of_dvd hdb p
  have hdcp : d ^ p ∣ c ^ p := by rw [← heq]; exact Nat.dvd_add hdap hdbp
  -- d | c via: set e = gcd(d,c), d'' = d/e, show d'' = 1
  have hdc : d ∣ c := by
    set e := Nat.gcd d c
    have hed : e ∣ d := Nat.gcd_dvd_left d c
    have hec : e ∣ c := Nat.gcd_dvd_right d c
    have he_pos : 0 < e := Nat.gcd_pos_of_pos_left c hd_pos
    set d'' := d / e
    set c'' := c / e
    have hd_eq : d = e * d'' := (Nat.mul_div_cancel' hed).symm
    have hc_eq : c = e * c'' := (Nat.mul_div_cancel' hec).symm
    have hd''_pos : 0 < d'' := Nat.div_pos (Nat.le_of_dvd hd_pos hed) he_pos
    -- Coprime(d'', c'') via gcd_mul_left
    have hd''c'' : Nat.Coprime d'' c'' := by
      unfold Nat.Coprime
      apply Nat.eq_of_mul_eq_mul_left he_pos
      rw [mul_one]
      calc e * Nat.gcd d'' c''
          = Nat.gcd (e * d'') (e * c'') := (Nat.gcd_mul_left e d'' c'').symm
        _ = Nat.gcd d c := by rw [Nat.mul_div_cancel' hed, Nat.mul_div_cancel' hec]
        _ = e := rfl
    -- d''^p | c''^p by canceling e^p from d^p | c^p
    have hep_pos : 0 < e ^ p := Nat.one_le_pow p e he_pos
    have hd''p_c''p : d'' ^ p ∣ c'' ^ p := by
      have h1 : e ^ p * d'' ^ p ∣ e ^ p * c'' ^ p := by
        rw [← mul_pow, ← mul_pow, ← hd_eq, ← hc_eq]; exact hdcp
      exact Nat.dvd_of_mul_dvd_mul_left hep_pos h1
    -- Coprime(d''^p, c''^p)
    have hcop_p : Nat.Coprime (d'' ^ p) (c'' ^ p) := hd''c''.pow_left p |>.pow_right p
    -- d''^p | 1, so d''^p = 1, so d'' = 1
    have hd''p1 : d'' ^ p = 1 := by
      have hdvd_gcd : d'' ^ p ∣ Nat.gcd (d'' ^ p) (c'' ^ p) :=
        Nat.dvd_gcd (dvd_refl _) hd''p_c''p
      have hdvd1 : d'' ^ p ∣ 1 := hcop_p ▸ hdvd_gcd
      exact Nat.eq_one_of_dvd_one hdvd1
    have hd''1 : d'' = 1 := by
      by_contra h
      have hge2 : 2 ≤ d'' := by omega
      have h1 : 2 ^ p ≤ d'' ^ p := Nat.pow_le_pow_left hge2 p
      have h2 : 2 ^ 5 ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) h5
      have h3 : (32 : ℕ) = 2 ^ 5 := by decide
      omega
    rw [hd_eq, hd''1, mul_one]
    exact hec
  -- Quotients
  set a' := a / d
  set b' := b / d
  set c' := c / d
  have ha'_eq : a = d * a' := (Nat.mul_div_cancel' hda).symm
  have hb'_eq : b = d * b' := (Nat.mul_div_cancel' hdb).symm
  have hc'_eq : c = d * c' := (Nat.mul_div_cancel' hdc).symm
  have ha'_pos : 0 < a' := Nat.div_pos (Nat.le_of_dvd ha hda) hd_pos
  have hb'_pos : 0 < b' := Nat.div_pos (Nat.le_of_dvd hb hdb) hd_pos
  have hc'_pos : 0 < c' := Nat.div_pos (Nat.le_of_dvd hc hdc) hd_pos
  -- Coprime(a', b') via gcd_mul_left
  have hab' : Nat.Coprime a' b' := by
    unfold Nat.Coprime
    apply Nat.eq_of_mul_eq_mul_left hd_pos
    rw [mul_one]
    calc d * Nat.gcd a' b'
        = Nat.gcd (d * a') (d * b') := (Nat.gcd_mul_left d a' b').symm
      _ = Nat.gcd a b := by rw [← ha'_eq, ← hb'_eq]
      _ = d := rfl
  -- a'^p + b'^p = c'^p
  have hdp_pos : 0 < d ^ p := Nat.one_le_pow p d hd_pos
  have heq' : a' ^ p + b' ^ p = c' ^ p := by
    apply Nat.eq_of_mul_eq_mul_left hdp_pos
    rw [mul_add, ← mul_pow, ← mul_pow, ← mul_pow, ← ha'_eq, ← hb'_eq, ← hc'_eq]
    exact heq
  -- Coprime(a', c'): if q | a' and q | c', then q | b'^p → q | b' → q | gcd(a',b') = 1
  have hac' : Nat.Coprime a' c' := by
    unfold Nat.Coprime
    by_contra h
    obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd h
    have hqa' : q ∣ a' := hqg.trans (Nat.gcd_dvd_left a' c')
    have hqc' : q ∣ c' := hqg.trans (Nat.gcd_dvd_right a' c')
    have hqap : q ∣ a' ^ p := dvd_pow hqa' (by omega)
    have hqcp : q ∣ c' ^ p := dvd_pow hqc' (by omega)
    have hqbp : q ∣ b' ^ p := by
      obtain ⟨s, hs⟩ : q ∣ a' ^ p + b' ^ p := heq'.symm ▸ hqcp
      obtain ⟨t, ht⟩ : q ∣ a' ^ p := hqap
      have hkey : b' ^ p + q * t = q * s := by omega
      have hts : t ≤ s := by
        have hle : q * t ≤ q * s := calc q * t = a' ^ p := ht.symm
          _ ≤ a' ^ p + b' ^ p := Nat.le_add_right _ _
          _ = q * s := hs
        exact Nat.le_of_mul_le_mul_left hle hq.pos
      exact ⟨s - t, by
        have h2 : q * (s - t) + q * t = q * s := by rw [← mul_add, Nat.sub_add_cancel hts]
        omega⟩
    have hqb' : q ∣ b' := hq.dvd_of_dvd_pow hqbp
    have hq1 : q ∣ Nat.gcd a' b' := Nat.dvd_gcd hqa' hqb'
    rw [hab'] at hq1
    have hq2 := hq.two_le
    exact absurd (Nat.le_of_dvd Nat.one_pos hq1) (by omega)
  -- Coprime(b', c'): symmetric
  have hbc' : Nat.Coprime b' c' := by
    unfold Nat.Coprime
    by_contra h
    obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd h
    have hqb' : q ∣ b' := hqg.trans (Nat.gcd_dvd_left b' c')
    have hqc' : q ∣ c' := hqg.trans (Nat.gcd_dvd_right b' c')
    have hqbp : q ∣ b' ^ p := dvd_pow hqb' (by omega)
    have hqcp : q ∣ c' ^ p := dvd_pow hqc' (by omega)
    have hqap : q ∣ a' ^ p := by
      obtain ⟨s, hs⟩ : q ∣ a' ^ p + b' ^ p := heq'.symm ▸ hqcp
      obtain ⟨t, ht⟩ : q ∣ b' ^ p := hqbp
      have hkey : a' ^ p + q * t = q * s := by omega
      have hts : t ≤ s := by
        have hle : q * t ≤ q * s := calc q * t = b' ^ p := ht.symm
          _ ≤ a' ^ p + b' ^ p := Nat.le_add_left _ _
          _ = q * s := hs
        exact Nat.le_of_mul_le_mul_left hle hq.pos
      exact ⟨s - t, by
        have h2 : q * (s - t) + q * t = q * s := by rw [← mul_add, Nat.sub_add_cancel hts]
        omega⟩
    have hqa' : q ∣ a' := hq.dvd_of_dvd_pow hqap
    have hq1 : q ∣ Nat.gcd a' b' := Nat.dvd_gcd hqa' hqb'
    rw [hab'] at hq1
    have hq2 := hq.two_le
    exact absurd (Nat.le_of_dvd Nat.one_pos hq1) (by omega)
  exact hcoprime a' b' c' ha'_pos hb'_pos hc'_pos hab' hbc' hac' heq'

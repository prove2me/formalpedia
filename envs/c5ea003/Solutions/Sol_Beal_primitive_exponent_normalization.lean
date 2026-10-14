-- Prove2me | solution 1 for Beal.primitive_exponent_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T03:51:27.573339+00:00
-- url     : https://prove2.me/submissions/ea5a093d-688f-4436-b63f-904931953b8d

import Mathlib.Data.Nat.Factors
import Mathlib.Algebra.GCDMonoid.Finset

private lemma reduce_exponent (A n : ℕ) (hA : A ≠ 0) (hn : 2 < n) :
    ∃ a p k : ℕ, a ≠ 0 ∧ 0 < k ∧
      (p = 4 ∨ Nat.Prime p ∧ Odd p) ∧ p ∣ n ∧
      a = A ^ k ∧ a ^ p = A ^ n := by
  obtain hd | ⟨p, hp, hd, ho⟩ :=
    Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn
  · obtain ⟨k, hk⟩ := hd
    refine ⟨A ^ k, 4, k, pow_ne_zero _ hA, ?_, Or.inl rfl, ⟨k, hk⟩, rfl, ?_⟩
    · by_contra h
      have : k = 0 := by omega
      simp [this] at hk
      omega
    · rw [← pow_mul, Nat.mul_comm k 4, ← hk]
  · obtain ⟨k, hk⟩ := hd
    refine ⟨A ^ k, p, k, pow_ne_zero _ hA, ?_, Or.inr ⟨hp, ho⟩,
      ⟨k, hk⟩, rfl, ?_⟩
    · by_contra h
      have : k = 0 := by omega
      simp [this] at hk
      omega
    · rw [← pow_mul, Nat.mul_comm k p, ← hk]

private lemma primitive_pairwise {A B C x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hg : Finset.gcd ({A, B, C} : Finset ℕ) id = 1)
    (he : A ^ x + B ^ y = C ^ z) :
    A.Coprime B ∧ A.Coprime C ∧ B.Coprime C := by
  have no_common (l : ℕ) (hl : Nat.Prime l)
      (ha : l ∣ A) (hb : l ∣ B) (hc : l ∣ C) : False := by
    have hd : l ∣ Finset.gcd ({A, B, C} : Finset ℕ) id := by
      apply Finset.dvd_gcd_iff.mpr
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl <;> assumption
    rw [hg] at hd
    exact hl.not_dvd_one hd
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    obtain ⟨l, hl, ha, hb⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    apply no_common l hl ha hb
    apply hl.dvd_of_dvd_pow (n := z)
    rw [← he]
    exact dvd_add (dvd_pow ha hx.ne') (dvd_pow hb hy.ne')
  · by_contra h
    obtain ⟨l, hl, ha, hc⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    apply no_common l hl ha _ hc
    apply hl.dvd_of_dvd_pow (n := y)
    apply (Nat.dvd_add_iff_right (dvd_pow ha hx.ne')).mpr
    rw [he]
    exact dvd_pow hc hz.ne'
  · by_contra h
    obtain ⟨l, hl, hb, hc⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    apply no_common l hl _ hb hc
    apply hl.dvd_of_dvd_pow (n := x)
    apply (Nat.dvd_add_iff_left (dvd_pow hb hy.ne')).mpr
    rw [he]
    exact dvd_pow hc hz.ne'

theorem solution (A B C x y z : ℕ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : 2 < x) (hy : 2 < y) (hz : 2 < z)
    (hg : Finset.gcd ({A, B, C} : Finset ℕ) id = 1)
    (he : A ^ x + B ^ y = C ^ z) :
    ∃ a b c p q r : ℕ,
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      (p = 4 ∨ Nat.Prime p ∧ Odd p) ∧
      (q = 4 ∨ Nat.Prime q ∧ Odd q) ∧
      (r = 4 ∨ Nat.Prime r ∧ Odd r) ∧
      p ∣ x ∧ q ∣ y ∧ r ∣ z ∧
      a ^ p = A ^ x ∧ b ^ q = B ^ y ∧ c ^ r = C ^ z ∧
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c := by
  obtain ⟨a, p, i, ha, hi, hp, hpx, hai, hap⟩ := reduce_exponent A x hA hx
  obtain ⟨b, q, j, hb, hj, hq, hqy, hbj, hbq⟩ := reduce_exponent B y hB hy
  obtain ⟨c, r, k, hc, hk, hr, hrz, hck, hcr⟩ := reduce_exponent C z hC hz
  obtain ⟨hab, hac, hbc⟩ := primitive_pairwise (by omega : 0 < x)
    (by omega : 0 < y) (by omega : 0 < z) hg he
  refine ⟨a, b, c, p, q, r, ha, hb, hc, hp, hq, hr,
    hpx, hqy, hrz, hap, hbq, hcr, ?_, ?_, ?_⟩
  · simpa [hai, hbj] using hab.pow i j
  · simpa [hai, hck] using hac.pow i k
  · simpa [hbj, hck] using hbc.pow j k

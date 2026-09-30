-- Prove2me | solution 1 for lean_workbook_plus_21087
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:32:00.716197+00:00
-- url     : https://prove2.me/submissions/feadbc9e-045f-4980-889d-7e9b0bfdadec

import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

private lemma consecutive_square_gap (y z t : ℕ) (ht : 0 < t) (htz : t < z) :
    y * (y + 1) ≠ z ^ 2 + t ∧ y * (y + 1) + t ≠ z ^ 2 := by
  constructor
  · intro he
    by_cases hy : y < z
    · have hp := Nat.mul_le_mul (Nat.le_of_lt hy) (Nat.succ_le_of_lt hy)
      nlinarith
    · have hyz : z ≤ y := by omega
      have hp := Nat.mul_le_mul hyz hyz
      nlinarith
  · intro he
    by_cases hy : y < z
    · have hyz : y + 1 ≤ z := by omega
      have h₁ := Nat.mul_le_mul_right z hyz
      have h₂ := Nat.mul_le_mul_left y hyz
      nlinarith
    · have hyz : z ≤ y := by omega
      have hp := Nat.mul_le_mul hyz hyz
      nlinarith

private lemma allocated_solution (c x y : ℕ) (hc : 1 < c)
    (he : x * (x + 1) = c ^ 2 * y * (y + 1))
    (hd : c ^ 2 ∣ x ∨ c ^ 2 ∣ x + 1) : x = 0 ∧ y = 0 := by
  have hc2 : 0 < c ^ 2 := pow_pos (by omega) _
  by_cases hx : x = 0
  · refine ⟨hx, ?_⟩
    by_contra hy
    have hpos : 0 < c ^ 2 * y * (y + 1) := by positivity
    simp only [hx, zero_mul] at he
    omega
  have hxpos : 0 < x := by omega
  exfalso
  rcases hd with ⟨t, ht⟩ | ⟨t, ht⟩
  · have htpos : 0 < t := by
      by_contra h
      have hz : t = 0 := by omega
      simp only [hz, mul_zero] at ht
      omega
    have htz : t < c * t := by nlinarith
    rw [ht] at he
    have hcancel : t * (c ^ 2 * t + 1) = y * (y + 1) :=
      Nat.eq_of_mul_eq_mul_left hc2 (by nlinarith [he])
    apply (consecutive_square_gap y (c * t) t htpos htz).1
    nlinarith [hcancel]
  · have htpos : 0 < t := by
      by_contra h
      have hz : t = 0 := by omega
      simp only [hz, mul_zero] at ht
      omega
    have htz : t < c * t := by nlinarith
    have hxt := congrArg (fun z : ℕ => z * t) ht
    rw [ht] at he
    have hcancel : x * t = y * (y + 1) :=
      Nat.eq_of_mul_eq_mul_left hc2 (by nlinarith [he])
    apply (consecutive_square_gap y (c * t) t htpos htz).2
    nlinarith [hcancel, hxt]

theorem natural_classification (p n x y : ℕ) (hp : p.Prime) (hn : 0 < n)
    (he : x * (x + 1) = p ^ (n * 2) * y * (y + 1)) : x = 0 ∧ y = 0 := by
  have hc : 1 < p ^ n := hp.one_lt.trans_le (Nat.le_self_pow hn.ne' p)
  have hd : p ^ (n * 2) ∣ x * (x + 1) := ⟨y * (y + 1), by rw [he]; ring⟩
  have halloc : p ^ (n * 2) ∣ x ∨ p ^ (n * 2) ∣ x + 1 := by
    by_cases hx : p ∣ x
    · have hnot : ¬p ∣ x + 1 := by
        intro h
        exact hp.not_dvd_one (by simpa using Nat.dvd_gcd hx h)
      exact Or.inl (hp.prime.pow_dvd_of_dvd_mul_right _ hnot hd)
    · exact Or.inr (hp.prime.pow_dvd_of_dvd_mul_left _ hx hd)
  apply allocated_solution (p ^ n) x y hc
  · simpa only [pow_mul] using he
  · simpa only [pow_mul] using halloc

private lemma integer_representative (z : ℤ) :
    ∃ u : ℕ, z = (u : ℤ) ∨ z = -(u : ℤ) - 1 := by
  by_cases hz : 0 ≤ z
  · exact ⟨z.toNat, Or.inl (Int.toNat_of_nonneg hz).symm⟩
  · refine ⟨(-z - 1).toNat, Or.inr ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    ring

theorem integer_solution_iff (p n : ℕ) (hp : p.Prime) (hn : 0 < n) (x y : ℤ) :
    x * (x + 1) = (p : ℤ) ^ (n * 2) * y * (y + 1) ↔
      (x = 0 ∨ x = -1) ∧ (y = 0 ∨ y = -1) := by
  constructor
  · intro he
    obtain ⟨u, hu⟩ := integer_representative x
    obtain ⟨v, hv⟩ := integer_representative y
    have hx : x * (x + 1) = (u : ℤ) * (u + 1) := by
      rcases hu with rfl | rfl <;> ring
    have hy : y * (y + 1) = (v : ℤ) * (v + 1) := by
      rcases hv with rfl | rfl <;> ring
    have heNat : u * (u + 1) = p ^ (n * 2) * v * (v + 1) := by
      have heInt : (u : ℤ) * (u + 1) = (p : ℤ) ^ (n * 2) * v * (v + 1) := by
        calc
          _ = x * (x + 1) := hx.symm
          _ = (p : ℤ) ^ (n * 2) * y * (y + 1) := he
          _ = (p : ℤ) ^ (n * 2) * (y * (y + 1)) := by ring
          _ = (p : ℤ) ^ (n * 2) * ((v : ℤ) * (v + 1)) := by rw [hy]
          _ = _ := by ring
      exact_mod_cast heInt
    obtain ⟨rfl, rfl⟩ := natural_classification p n u v hp hn heNat
    simpa using And.intro hu hv
  · rintro ⟨rfl | rfl, rfl | rfl⟩ <;> simp

theorem solution : ¬(∀ (p n : ℕ), p.Prime → 0 < n →
    ¬(∃ x y : ℤ, x * (x + 1) = p ^ (n * 2) * y * (y + 1))) := by
  intro h
  apply h 2 1 (by norm_num) (by norm_num)
  exact ⟨0, 0, (integer_solution_iff 2 1 (by norm_num) (by norm_num) 0 0).mpr
    ⟨Or.inl rfl, Or.inl rfl⟩⟩

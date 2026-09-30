-- Prove2me | solution 1 for lean_workbook_plus_80511
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:09:43.927918+00:00
-- url     : https://prove2.me/submissions/6cb74cae-efaf-4fda-b6a6-5b22c6bb182a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Ring

namespace DyadicPowerSumDivisibility

theorem quartic_identity {R : Type*} [CommSemiring R] (a b c : R) :
    a ^ 4 + b ^ 4 + c ^ 4 +
        (a * b + a * c + b * c) * (a ^ 2 + b ^ 2 + c ^ 2) =
      (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3 + a * b * c) := by
  ring

theorem fourth_power_sum_dvd {R : Type*} [CommRing R] (m a b c : R)
    (h1 : m ∣ a + b + c) (h2 : m ∣ a ^ 2 + b ^ 2 + c ^ 2) :
    m ∣ a ^ 4 + b ^ 4 + c ^ 4 := by
  have hd : m ∣ (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3 + a * b * c) -
      (a * b + a * c + b * c) * (a ^ 2 + b ^ 2 + c ^ 2) :=
    dvd_sub (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)
  rw [← quartic_identity] at hd
  simpa using hd

theorem dyadic_pair {R : Type*} [CommRing R] (m a b c : R)
    (h1 : m ∣ a + b + c) (h2 : m ∣ a ^ 2 + b ^ 2 + c ^ 2) (k : ℕ) :
    (m ∣ a ^ (2 ^ k) + b ^ (2 ^ k) + c ^ (2 ^ k)) ∧
      (m ∣ a ^ (2 ^ (k + 1)) + b ^ (2 ^ (k + 1)) + c ^ (2 ^ (k + 1))) := by
  induction k with
  | zero => simpa using And.intro h1 h2
  | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hsq : m ∣ (a ^ (2 ^ k)) ^ 2 + (b ^ (2 ^ k)) ^ 2 +
          (c ^ (2 ^ k)) ^ 2 := by
        simpa only [pow_succ, pow_mul] using ih.2
      have hfour := fourth_power_sum_dvd m (a ^ (2 ^ k)) (b ^ (2 ^ k))
        (c ^ (2 ^ k)) ih.1 hsq
      have hexp : 2 ^ (k + 1 + 1) = 2 ^ k * 4 := by
        simp only [pow_succ]
        ring
      simpa only [hexp, pow_mul] using hfour

theorem infinitely_many {R : Type*} [CommRing R] (m a b c : R)
    (h1 : m ∣ a + b + c) (h2 : m ∣ a ^ 2 + b ^ 2 + c ^ 2) :
    {n : ℕ | 0 < n ∧ m ∣ a ^ n + b ^ n + c ^ n}.Infinite := by
  have hrange : (Set.range (fun k : ℕ => (2 : ℕ) ^ k)).Infinite :=
    Set.infinite_range_of_injective
      (pow_right_strictMono₀ (show 1 < (2 : ℕ) by decide)).injective
  apply hrange.mono
  rintro n ⟨k, rfl⟩
  exact ⟨pow_pos (by decide : 0 < (2 : ℕ)) k, (dyadic_pair m a b c h1 h2 k).1⟩

theorem source_infinite (a b c : ℤ)
    (h : a + b + c ∣ a ^ 2 + b ^ 2 + c ^ 2) :
    {n : ℕ | 0 < n ∧ a + b + c ∣ a ^ n + b ^ n + c ^ n}.Infinite :=
  infinitely_many (a + b + c) a b c (dvd_refl _) h

end DyadicPowerSumDivisibility

theorem solution (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a + b + c ∣ a ^ 2 + b ^ 2 + c ^ 2) :
    ∃ n : ℕ, a + b + c ∣ a ^ n + b ^ n + c ^ n := by
  obtain ⟨n, _, hn⟩ := (DyadicPowerSumDivisibility.source_infinite a b c habc).nonempty
  exact ⟨n, hn⟩

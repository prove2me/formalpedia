-- Prove2me | solution 1 for Bridges.AlexanderTorus.prod_cyclotomic_two_mul_divisors
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T14:50:44.536628+00:00
-- url     : https://prove2.me/submissions/9385b168-b1ae-47b9-96b2-7ef59965806e

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

lemma divisors_two_mul {N : ℕ} (hpos : 0 < N) :
    (2 * N).divisors = N.divisors ∪ (N.divisors.image (fun d => 2 * d)) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hdvd, -⟩
    rcases Nat.even_or_odd d with he | ho
    · obtain ⟨e, rfl⟩ := he
      refine Or.inr ⟨e, ⟨?_, hpos.ne'⟩, by ring⟩
      have h : (2 : ℕ) * e ∣ 2 * N := by simpa [two_mul] using hdvd
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 h
    · exact Or.inl ⟨Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.2 ho) hdvd,
        hpos.ne'⟩
  · rintro (⟨hdvd, -⟩ | ⟨e, ⟨he, -⟩, rfl⟩)
    · exact ⟨hdvd.mul_left 2, by positivity⟩
    · exact ⟨mul_dvd_mul_left 2 he, by positivity⟩

lemma disjoint_divisors_image_two_mul {N : ℕ} (hN : Odd N) :
    Disjoint N.divisors (N.divisors.image (fun d => 2 * d)) := by
  rw [Finset.disjoint_right]
  rintro a ha ha'
  simp only [Finset.mem_image, Nat.mem_divisors] at ha ha'
  obtain ⟨e, -, rfl⟩ := ha
  obtain ⟨hdvd, -⟩ := ha'
  obtain ⟨k, hk⟩ := (dvd_mul_right 2 e).trans hdvd
  rw [Nat.odd_iff] at hN
  omega

/-! ## The cyclotomic factorization -/

theorem solution {N : ℕ} (hN : Odd N) (hpos : 0 < N) :
    ∏ d ∈ N.divisors, cyclotomic (2 * d) ℤ = X ^ N + 1 := by
  have key : (∏ d ∈ N.divisors, cyclotomic d ℤ) * (∏ d ∈ N.divisors, cyclotomic (2 * d) ℤ)
      = X ^ (2 * N) - 1 := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one (by omega) ℤ, divisors_two_mul hpos,
      Finset.prod_union (disjoint_divisors_image_two_mul hN),
      Finset.prod_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by norm_num) h)]
  rw [prod_cyclotomic_eq_X_pow_sub_one hpos ℤ] at key
  have hne : (X ^ N - 1 : ℤ[X]) ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp [zero_pow hpos.ne'] at h0
  refine mul_left_cancel₀ hne ?_
  rw [key, two_mul, pow_add]
  ring

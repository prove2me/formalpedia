-- Prove2me | solution 1 for polynomial_goldbach_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:20:08.368548+00:00
-- url     : https://prove2.me/submissions/6465ff21-3f57-4452-bda3-b7690a68823f

import Mathlib

/- Complete source: Main.lean; SHA256: da409291c68946bc4ab635a83aacfb7a34094c7f326946f91079ac2dba1037b8. -/
section BundledMain
namespace PolynomialGoldbach

open Polynomial

noncomputable def raised (p : Polynomial ℤ) (a b : ℤ) : Polynomial ℤ :=
  X ^ (p.natDegree + 1) + (C a * p + C b)

theorem lower_natDegree (p : Polynomial ℤ) (a b : ℤ) :
    (C a * p + C b).natDegree < p.natDegree + 1 := by
  apply lt_of_le_of_lt (natDegree_add_le _ _)
  exact lt_of_le_of_lt (max_le (natDegree_C_mul_le a p) (by simp))
    (Nat.lt_succ_self _)

theorem raised_monic (p : Polynomial ℤ) (a b : ℤ) : (raised p a b).Monic := by
  apply (monic_X_pow (p.natDegree + 1)).add_of_left
  apply degree_lt_degree
  simpa using lower_natDegree p a b

theorem raised_natDegree (p : Polynomial ℤ) (a b : ℤ) :
    (raised p a b).natDegree = p.natDegree + 1 := by
  unfold raised
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · simpa using lower_natDegree p a b

theorem raised_coeff_low (p : Polynomial ℤ) (a b : ℤ) {n : ℕ}
    (hn : n < p.natDegree + 1) :
    (raised p a b).coeff n = a * p.coeff n + if n = 0 then b else 0 := by
  simp only [raised, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    if_neg (ne_of_lt hn), zero_add]

theorem raised_coeff_zero (p : Polynomial ℤ) (a b : ℤ) :
    (raised p a b).coeff 0 = a * p.coeff 0 + b := by
  simpa using raised_coeff_low p a b (Nat.zero_lt_succ p.natDegree)

theorem raised_irreducible (p : Polynomial ℤ) (a b prime : ℤ)
    (hp : Prime prime) (ha : prime ∣ a) (hb : prime ∣ b)
    (hzero : ¬ prime ^ 2 ∣ a * p.coeff 0 + b) : Irreducible (raised p a b) := by
  have hI : (Ideal.span ({prime} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hm := raised_monic p a b
  have he : (raised p a b).IsEisensteinAt (Ideal.span ({prime} : Set ℤ)) := by
    refine ⟨hm.leadingCoeff_notMem hI.ne_top, ?_, ?_⟩
    · intro n hn
      rw [raised_natDegree] at hn
      rw [raised_coeff_low p a b hn, Ideal.mem_span_singleton]
      apply dvd_add (dvd_mul_of_dvd_left ha _)
      split_ifs
      · exact hb
      · exact dvd_zero _
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, raised_coeff_zero]
      exact hzero
  apply he.irreducible hI hm.isPrimitive
  rw [raised_natDegree]
  exact Nat.zero_lt_succ _

-- Either odd shift makes the first polynomial Eisenstein at 2; choose between
-- them so that the second polynomial's constant coefficient is not divisible by 9.
theorem exists_shift (z : ℤ) :
    ∃ t : ℤ, (t = 1 ∨ t = 3) ∧
      ¬ 4 ∣ 4 * z + 6 * t ∧ ¬ 9 ∣ 3 * z + 6 * t := by
  by_cases hz : 3 ∣ z + 2
  · refine ⟨3, Or.inr rfl, ?_, ?_⟩
    · rw [Int.dvd_iff_emod_eq_zero]
      omega
    · rw [Int.dvd_iff_emod_eq_zero] at hz ⊢
      omega
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · rw [Int.dvd_iff_emod_eq_zero]
      omega
    · rw [Int.dvd_iff_emod_eq_zero] at hz ⊢
      omega

theorem exists_irreducible_sum (p : Polynomial ℤ) :
    ∃ q r : Polynomial ℤ, Irreducible q ∧ Irreducible r ∧ p = q + r := by
  obtain ⟨t, _, htwo, hthree⟩ := exists_shift (p.coeff 0)
  have hq : Irreducible (raised p 4 (6 * t)) := by
    apply raised_irreducible p 4 (6 * t) 2 (by norm_num) (by norm_num)
    · exact dvd_mul_of_dvd_left (by norm_num : (2 : ℤ) ∣ 6) t
    · simpa using htwo
  have hg : Irreducible (raised p 3 (6 * t)) := by
    apply raised_irreducible p 3 (6 * t) 3 (by norm_num) (dvd_refl _)
    · exact dvd_mul_of_dvd_left (by norm_num : (3 : ℤ) ∣ 6) t
    · simpa using hthree
  refine ⟨raised p 4 (6 * t), -raised p 3 (6 * t), hq, ?_, ?_⟩
  · simpa only [neg_one_mul] using
      (irreducible_isUnit_mul (show IsUnit (-1 : Polynomial ℤ) by simp)).mpr hg
  · unfold raised
    norm_num
    ring

end PolynomialGoldbach

theorem solution (p : Polynomial ℤ)
    (hdeg : 2 ≤ p.natDegree)
    (hirr : Irreducible p)
    (hlc : 0 < p.leadingCoeff) :
    ∃ (q r : Polynomial ℤ),
      Irreducible q ∧ Irreducible r ∧ p = q + r := by
  clear hdeg hirr hlc
  exact PolynomialGoldbach.exists_irreducible_sum p
end BundledMain

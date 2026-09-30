-- Prove2me | solution 1 for lean_workbook_plus_67848
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:23:06.950429+00:00
-- url     : https://prove2.me/submissions/88217349-4130-469c-a6e4-f13c549b9882

import Mathlib

namespace CyclicDegreeFiveAMGM

theorem weighted_root (A B C t : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ht : 0 ≤ t) (hp : t ^ 7 = A ^ 4 * B * C ^ 2) :
    A ^ (4 / 7 : ℝ) * B ^ (1 / 7 : ℝ) * C ^ (2 / 7 : ℝ) = t := by
  apply (pow_left_inj₀ (by positivity) ht (by decide : (7 : ℕ) ≠ 0)).mp
  rw [hp, mul_pow, mul_pow,
    ← Real.rpow_mul_natCast hA (4 / 7 : ℝ) 7,
    ← Real.rpow_mul_natCast hB (1 / 7 : ℝ) 7,
    ← Real.rpow_mul_natCast hC (2 / 7 : ℝ) 7]
  rw [show (4 / 7 : ℝ) * (7 : ℕ) = (4 : ℕ) by norm_num,
    show (1 / 7 : ℝ) * (7 : ℕ) = 1 by norm_num,
    show (2 / 7 : ℝ) * (7 : ℕ) = (2 : ℕ) by norm_num,
    Real.rpow_natCast, Real.rpow_one, Real.rpow_natCast]

theorem weighted_bound (A B C t : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ht : 0 ≤ t) (hp : t ^ 7 = A ^ 4 * B * C ^ 2) : 7 * t ≤ 4 * A + B + 2 * C := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (by norm_num : (0 : ℝ) ≤ 4 / 7) (by norm_num : (0 : ℝ) ≤ 1 / 7)
    (by norm_num : (0 : ℝ) ≤ 2 / 7) hA hB hC (by norm_num)
  rw [weighted_root A B C t hA hB hC ht hp] at h
  linarith

theorem weighted_equality (A B C t : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ht : 0 ≤ t) (hp : t ^ 7 = A ^ 4 * B * C ^ 2)
    (he : 7 * t = 4 * A + B + 2 * C) : A = B ∧ B = C := by
  let w : Fin 3 → ℝ := ![4 / 7, 1 / 7, 2 / 7]
  let z : Fin 3 → ℝ := ![A, B, C]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 < w i := by
    intro i _
    fin_cases i <;> norm_num [w]
  have hws : ∑ i : Fin 3, w i = 1 := by norm_num [w, Fin.sum_univ_succ]; rfl
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ z i := by
    intro i _
    fin_cases i <;> assumption
  have he' : A ^ (4 / 7 : ℝ) * B ^ (1 / 7 : ℝ) * C ^ (2 / 7 : ℝ) =
      (4 / 7) * A + (1 / 7) * B + (2 / 7) * C := by
    rw [weighted_root A B C t hA hB hC ht hp]
    linarith
  have he'' : ∏ i : Fin 3, z i ^ w i = ∑ i : Fin 3, w i * z i := by
    simpa [w, z, Fin.prod_univ_succ, Fin.sum_univ_succ, mul_assoc, add_assoc] using he'
  have hall := (Real.geom_mean_eq_arith_mean_weighted_iff' Finset.univ w z hw hws hz).mp he''
  have h0 := hall 0 (by simp)
  have h1 := hall 1 (by simp)
  have h2 := hall 2 (by simp)
  exact ⟨h0.trans h1.symm, h1.trans h2.symm⟩

theorem homogeneous_bound (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ 2 * y ^ 2 * z + x ^ 2 * y * z ^ 2 + x * y ^ 2 * z ^ 2 ≤
      x ^ 3 * y ^ 2 + x ^ 2 * z ^ 3 + y ^ 3 * z ^ 2 := by
  have h1 := weighted_bound (x ^ 3 * y ^ 2) (x ^ 2 * z ^ 3) (y ^ 3 * z ^ 2)
    (x ^ 2 * y ^ 2 * z) (by positivity) (by positivity) (by positivity) (by positivity) (by ring)
  have h2 := weighted_bound (x ^ 2 * z ^ 3) (y ^ 3 * z ^ 2) (x ^ 3 * y ^ 2)
    (x ^ 2 * y * z ^ 2) (by positivity) (by positivity) (by positivity) (by positivity) (by ring)
  have h3 := weighted_bound (y ^ 3 * z ^ 2) (x ^ 3 * y ^ 2) (x ^ 2 * z ^ 3)
    (x * y ^ 2 * z ^ 2) (by positivity) (by positivity) (by positivity) (by positivity) (by ring)
  linarith

theorem source_bound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 2 * y ^ 2 + x ^ 2 * y + x * y ^ 2 ≤ x ^ 3 * y ^ 2 + x ^ 2 + y ^ 3 := by
  simpa using homogeneous_bound x y 1 hx hy (by norm_num)

theorem equality_iff (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 2 * y ^ 2 + x ^ 2 * y + x * y ^ 2 = x ^ 3 * y ^ 2 + x ^ 2 + y ^ 3 ↔
      (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) := by
  constructor
  · intro he
    by_cases hx0 : x = 0
    · subst x
      have hy3 : y ^ 3 = 0 := by nlinarith
      exact Or.inl ⟨rfl, (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hy3⟩
    by_cases hy0 : y = 0
    · subst y
      have hx2 : x ^ 2 = 0 := by nlinarith
      exact Or.inl ⟨(pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hx2, rfl⟩
    have h1 := weighted_bound (x ^ 3 * y ^ 2) (x ^ 2) (y ^ 3)
      (x ^ 2 * y ^ 2) (by positivity) (by positivity) (by positivity) (by positivity) (by ring)
    have h2 := weighted_bound (x ^ 2) (y ^ 3) (x ^ 3 * y ^ 2)
      (x ^ 2 * y) (by positivity) (by positivity) (by positivity) (by positivity) (by ring)
    have h3 := weighted_bound (y ^ 3) (x ^ 3 * y ^ 2) (x ^ 2)
      (x * y ^ 2) (by positivity) (by positivity) (by positivity) (by positivity) (by ring)
    have he1 : 7 * (x ^ 2 * y ^ 2) = 4 * (x ^ 3 * y ^ 2) + x ^ 2 + 2 * y ^ 3 := by
      linarith
    obtain ⟨hAB, hBC⟩ := weighted_equality (x ^ 3 * y ^ 2) (x ^ 2) (y ^ 3)
      (x ^ 2 * y ^ 2) (by positivity) (by positivity) (by positivity) (by positivity) (by ring) he1
    have hprod : x ^ 2 * (x * y ^ 2 - 1) = 0 := by linear_combination hAB
    have hxy : x * y ^ 2 = 1 := by
      have hh := (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 hx0)
      linarith
    have hs : (x * y ^ 2) ^ 2 = 1 := by rw [hxy]; ring
    have hy7 : y ^ 7 = 1 := by
      calc y ^ 7 = y ^ 3 * y ^ 4 := by ring
           _ = x ^ 2 * y ^ 4 := by rw [hBC]
           _ = 1 := by nlinarith [hs]
    have hy1 : y = 1 := (pow_left_inj₀ hy (by norm_num : (0 : ℝ) ≤ 1)
      (by decide : (7 : ℕ) ≠ 0)).mp (by simpa using hy7)
    subst y
    exact Or.inr ⟨by simpa using hxy, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ring

end CyclicDegreeFiveAMGM

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 2 * y ^ 2 + x ^ 2 * y + x * y ^ 2 ≤ x ^ 3 * y ^ 2 + x ^ 2 + y ^ 3 :=
  CyclicDegreeFiveAMGM.source_bound x y hx hy

#print axioms CyclicDegreeFiveAMGM.weighted_root
#print axioms CyclicDegreeFiveAMGM.weighted_bound
#print axioms CyclicDegreeFiveAMGM.weighted_equality
#print axioms CyclicDegreeFiveAMGM.homogeneous_bound
#print axioms CyclicDegreeFiveAMGM.source_bound
#print axioms CyclicDegreeFiveAMGM.equality_iff
#print axioms solution

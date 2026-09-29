-- Prove2me | solution 1 for mme_stothers_globalRate_correction_factor_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-07T15:37:23.578379+00:00
-- url     : https://prove2.me/submissions/96ffee91-6716-4350-8ad9-ae28a5a9550f

import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_stothers_lemma52_same_marginal

open MME BigOperators

universe u

set_option autoImplicit false

namespace P2MGain

open MME.StothersFourth

/-- `E`, `H` and `L` of Lemma 5.1 are nonnegative for every `q` and `tau`. -/
theorem EHL_nonneg (q : ℕ) (tau : ℝ) :
    0 ≤ E q tau ∧ 0 ≤ H q tau ∧ 0 ≤ L q tau := by
  refine ⟨Real.rpow_nonneg (by positivity) _, Real.rpow_nonneg (by positivity) _, ?_⟩
  have h : (0 : ℝ) ≤ (q : ℝ) ^ (3 * tau) := Real.rpow_nonneg (by positivity) _
  unfold L
  positivity

theorem classValue_nonneg (q : ℕ) (tau : ℝ) (i : Fin 10) :
    0 ≤ classValue q tau i := by
  obtain ⟨hE, hH, hL⟩ := EHL_nonneg q tau
  have h4E : (0:ℝ) ≤ 2 + 2 * E q tau + H q tau := by linarith
  have h2HL : (0:ℝ) ≤ 2 * H q tau + L q tau := by linarith
  have hLEH : (0:ℝ) ≤ L q tau + E q tau * H q tau := by nlinarith
  have hEL : (0:ℝ) ≤ E q tau + L q tau := by linarith
  fin_cases i <;>
    simp only [classValue] <;> norm_num <;>
    positivity

theorem marginal_nonneg {a : Fin 10 → ℝ} (ha : ∀ i, 0 ≤ a i) (j : Fin 9) :
    0 ≤ marginal a j := by
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2; have h3 := ha 3; have h4 := ha 4
  have h5 := ha 5; have h6 := ha 6; have h7 := ha 7; have h8 := ha 8; have h9 := ha 9
  fin_cases j <;> simp only [marginal, Q] <;> norm_num <;> linarith

theorem rpow_eq (x y : ℝ) : Real.rpow x y = x ^ y := rfl

theorem prod_rpow_npow (x : Fin 10 → ℝ) (hx : ∀ i, 0 < x i) (f : Fin 10 → ℝ) :
    (∏ i : Fin 10, (Real.rpow (x i) (f i)) ^ (classMultiplicity i)) =
      ∏ i : Fin 10, Real.rpow (x i) ((classMultiplicity i : ℝ) * f i) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [rpow_eq]
  rw [← Real.rpow_natCast ((x i) ^ (f i)) (classMultiplicity i),
    ← Real.rpow_mul (hx i).le]
  congr 1
  ring

theorem entropyProduct_pos {x : Fin 10 → ℝ} (hx : ∀ i, 0 < x i) :
    0 < entropyProduct x :=
  Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _

theorem globalRate_self_nonneg (q : ℕ) (tau : ℝ) {a : Fin 10 → ℝ}
    (ha : ∀ i, 0 ≤ a i) : 0 ≤ globalRate q tau a a := by
  unfold globalRate
  refine mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg ?_ _)
    (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (marginal_nonneg ha j) _)
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (classValue_nonneg q tau i) _)
    (Real.rpow_nonneg (ha i) _)) (Real.rpow_nonneg (ha i) _)

end P2MGain

open P2MGain MME.StothersFourth in
theorem solution
    (q : ℕ) (tau : ℝ) (a b : Fin 10 → ℝ)
    (ha : MME.StothersFourth.InZ a) (hb : MME.StothersFourth.InN b)
    (haPos : ∀ i : Fin 10, 0 < a i) (hbPos : ∀ i : Fin 10, 0 < b i)
    (hsame : MME.StothersFourth.InY (fun i => a i - b i)) :
    MME.StothersFourth.globalRate q tau a b =
        MME.StothersFourth.globalRate q tau a a *
          (MME.StothersFourth.entropyProduct a /
            MME.StothersFourth.entropyProduct b) ∧
      1 ≤ MME.StothersFourth.entropyProduct a /
            MME.StothersFourth.entropyProduct b ∧
      MME.StothersFourth.globalRate q tau a a ≤
        MME.StothersFourth.globalRate q tau a b := by
  have hEa : 0 < entropyProduct a := entropyProduct_pos haPos
  have hEb : 0 < entropyProduct b := entropyProduct_pos hbPos
  have h52 : entropyProduct b ≤ entropyProduct a :=
    mme_stothers_lemma52_same_marginal.2 a b ha hb hbPos hsame
  have hratio : 1 ≤ entropyProduct a / entropyProduct b := (one_le_div hEb).2 h52
  have hnn : 0 ≤ globalRate q tau a a := globalRate_self_nonneg q tau ha.1
  set C : ℝ := ∏ i : Fin 10,
    (Real.rpow (classValue q tau i) (a i / 3)) ^ (classMultiplicity i) with hC
  set M : ℝ := ∏ j : Fin 9, Real.rpow (marginal a j) (-marginal a j) with hM
  have hself : globalRate q tau a a = C * M := by
    rw [globalRate, hC, hM]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : Real.rpow (a i) (a i) * Real.rpow (a i) (-a i) = 1 := by
      simp only [rpow_eq]
      rw [← Real.rpow_add (haPos i)]
      simp
    rw [mul_assoc, h1, mul_one]
  have hcross : globalRate q tau a b =
      C * (entropyProduct a / entropyProduct b) * M := by
    rw [globalRate, hC, hM]
    have hsplit : ∀ i : Fin 10,
        (Real.rpow (classValue q tau i) (a i / 3) * Real.rpow (a i) (a i) *
              Real.rpow (b i) (-b i)) ^ (classMultiplicity i) =
          ((Real.rpow (classValue q tau i) (a i / 3)) ^ (classMultiplicity i)) *
            ((Real.rpow (a i) (a i)) ^ (classMultiplicity i)) *
            ((Real.rpow (b i) (-b i)) ^ (classMultiplicity i)) := by
      intro i; rw [mul_pow, mul_pow]
    rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => hsplit i),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hA : (∏ i : Fin 10, (Real.rpow (a i) (a i)) ^ (classMultiplicity i)) =
        entropyProduct a := prod_rpow_npow a haPos a
    have hB : (∏ i : Fin 10, (Real.rpow (b i) (-b i)) ^ (classMultiplicity i)) =
        (entropyProduct b)⁻¹ := by
      rw [prod_rpow_npow b hbPos (fun i => -b i), entropyProduct,
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [rpow_eq]
      rw [← Real.rpow_neg (hbPos i).le]
      congr 1
      ring
    rw [hA, hB]
    field_simp
  refine ⟨by rw [hcross, hself]; ring, hratio, ?_⟩
  rw [hcross, hself]
  have hCM : 0 ≤ C * M := hself ▸ hnn
  nlinarith [hratio, hCM]

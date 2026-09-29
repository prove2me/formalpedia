-- Prove2me | solution 1 for mme_common_hash_scale_realization
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T16:35:24.834987+00:00
-- url     : https://prove2.me/submissions/4a02c538-6871-4931-aa4c-b13534c2fe5d

import Definitions.Def_mme_common_hash_scale
import Theorems.Thm_mme_prime_half_modulus_behrend

open MME.RegionRealization
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem solution {J : Type*} [Fintype J]
    (grade : ℕ) (num den : J → ℕ) (hden : ∀ j, 0 < den j) :
    let Q := commonScale grade num den
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ grade < p ∧ 2 * Q < p ∧ p ≤ 4 * Q ∧
      (∀ j, num j ≤ p * den j) ∧
      ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧ ThreeAPFree (S : Set ℕ) ∧
        (Q : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) ≤ (S.card : ℝ) ∧
        ∀ T I : ℝ, 0 ≤ T → T * S.card / (2 * (p : ℝ) ^ 2) ≤ I →
          T * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ I := by
  classical
  let Q := commonScale grade num den
  have hg : grade + 1 ≤ Q := le_max_left _ _
  have hQ : 0 < Q := by omega
  obtain ⟨p, hp, hlow, hupp, S, hSr, hSf, hSc⟩ := mme_prime_half_modulus_behrend Q hQ
  have hpgt : 2 < p := by omega
  refine ⟨p, hp, hp.odd_of_ne_two (by omega), by omega, hlow, hupp, ?_, S, hSr, hSf, hSc, ?_⟩
  · intro j
    have hr : num j / den j + 1 ≤ Q :=
      (Finset.le_sup (f := fun j ↦ num j / den j + 1) (Finset.mem_univ j)).trans (le_max_right _ _)
    have hdiv : num j / den j < p := by omega
    exact (Nat.div_lt_iff_lt_mul (hden j)).mp hdiv |>.le
  · intro T I hT hI
    have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hprQ : (p : ℝ) ≤ 4 * Q := by exact_mod_cast hupp
    have hp2 : (p : ℝ) ^ 2 ≤ 16 * (Q : ℝ) ^ 2 := by nlinarith
    have hE := Real.exp_pos (-4 * Real.sqrt (Real.log Q))
    have hS : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hI' := (div_le_iff₀ (show (0 : ℝ) < 2 * (p : ℝ) ^ 2 by positivity)).mp hI
    have hInonneg : 0 ≤ I := le_trans (by positivity) hI
    apply (div_le_iff₀ (show (0 : ℝ) < 32 * (Q : ℝ) by positivity)).mpr
    have h1 := mul_le_mul_of_nonneg_left hSc hT
    have h2 := mul_le_mul_of_nonneg_left hp2 hInonneg
    nlinarith [mul_pos hQr hE]

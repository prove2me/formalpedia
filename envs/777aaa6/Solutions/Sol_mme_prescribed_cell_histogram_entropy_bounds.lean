-- Prove2me | solution 1 for mme_prescribed_cell_histogram_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T16:35:23.773919+00:00
-- url     : https://prove2.me/submissions/cc1019b2-89e0-4b70-b7b0-d618da20adf5

import Definitions.Def_mme_region_count_entropy_data
import Theorems.Thm_mme_dwz_multinomial_entropy_upper
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower

open BigOperators MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem row_bounds {W : Type*} [Fintype W]
    (w : W → ℕ) (m : ℕ) (hm : 0 < m) :
    (Nat.multinomial Finset.univ (fun i ↦ w i * m) : ℝ) ≤
      Real.exp ((m : ℝ) * (((∑ i, w i : ℕ) : ℝ) * Real.log 2 *
        mme_modern_entropyBits (fun i ↦ (w i : ℝ) / ((∑ j, w j : ℕ) : ℝ)))) ∧
    Real.exp ((m : ℝ) * (((∑ i, w i : ℕ) : ℝ) * Real.log 2 *
        mme_modern_entropyBits (fun i ↦ (w i : ℝ) / ((∑ j, w j : ℕ) : ℝ)))) ≤
      (6 * (((∑ i, w i) * m + 1 : ℕ) : ℝ)) ^ Fintype.card W *
        (Nat.multinomial Finset.univ (fun i ↦ w i * m) : ℝ) := by
  classical
  by_cases h : 0 < ∑ i, w i
  · exact ⟨mme_dwz_multinomial_entropy_upper w m hm h,
      mme_dwz_multinomial_entropy_polynomial_lower w m hm h⟩
  · have hz : ∑ i, w i = 0 := by omega
    have hw : ∀ i, w i = 0 := by
      intro i
      exact Nat.eq_zero_of_le_zero (by simpa [hz] using (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (w j)) (Finset.mem_univ i)))
    simp only [hw, Finset.sum_const_zero, Nat.cast_zero, zero_mul, Real.exp_zero,
      Nat.zero_add, Nat.cast_one, mul_one]
    have hmult : Nat.multinomial Finset.univ (fun _ : W ↦ 0 * m) = 1 := by
      simp [Nat.multinomial]
    simpa [Nat.multinomial, Real.exp_zero] using (show (1 : ℝ) ≤ 1 ∧ 1 ≤ (6 : ℝ) ^ Fintype.card W from ⟨le_rfl, one_le_pow₀ (by norm_num)⟩)

theorem solution {C W : Type*} [Fintype C] [Fintype W]
    (mu : C → W → ℕ) (m : ℕ) (hm : 0 < m) :
    (histogramNumber (fun c w ↦ mu c w * m) : ℝ) ≤ Real.exp ((m : ℝ) * potential mu) ∧
    Real.exp ((m : ℝ) * potential mu) ≤
      errorFactor mu m * (histogramNumber (fun c w ↦ mu c w * m) : ℝ) := by
  classical
  have hc : (histogramNumber (fun c w ↦ mu c w * m) : ℝ) =
      ∏ c, (Nat.multinomial Finset.univ (fun w ↦ mu c w * m) : ℝ) := by
    simp only [histogramNumber, Nat.cast_prod, Nat.multinomial]
  have he : Real.exp ((m : ℝ) * potential mu) =
      ∏ c, Real.exp ((m : ℝ) * (((∑ w, mu c w : ℕ) : ℝ) * Real.log 2 *
        mme_modern_entropyBits (fun w ↦ (mu c w : ℝ) / ((∑ z, mu c z : ℕ) : ℝ)))) := by
    rw [potential, Finset.mul_sum, Real.exp_sum]
  rw [hc, he]
  constructor
  · exact Finset.prod_le_prod (fun _ _ ↦ Nat.cast_nonneg _) (fun c _ ↦ (row_bounds (mu c) m hm).1)
  · calc
      _ ≤ ∏ c, (6 * (((∑ w, mu c w) * m + 1 : ℕ) : ℝ)) ^ Fintype.card W *
          (Nat.multinomial Finset.univ (fun w ↦ mu c w * m) : ℝ) :=
        Finset.prod_le_prod (fun _ _ ↦ (Real.exp_pos _).le) (fun c _ ↦ (row_bounds (mu c) m hm).2)
      _ = _ := Finset.prod_mul_distrib

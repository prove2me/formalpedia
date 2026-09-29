-- Prove2me | solution 1 for mme_dwz_typical_denominator_entropy_upper_of_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T11:54:28.929992+00:00
-- url     : https://prove2.me/submissions/c80e49fa-6fd2-4afc-9330-9cfd14fb6918

import Mathlib
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_multinomial_entropy_upper

open scoped BigOperators
set_option autoImplicit false

theorem solution
    {Fine Coarse : Type*} [Fintype Fine] [Fintype Coarse]
    (gamma : Fine → ℕ) (alphaZ : Coarse → ℕ)
    (m : ℕ) (hm : 0 < m)
    (hsum : ∑ i, gamma i = ∑ k, alphaZ k)
    (hW : 0 < ∑ i, gamma i)
    (B : ℕ)
    (hfactor :
      Nat.multinomial Finset.univ (fun i ↦ gamma i * m) =
        Nat.multinomial Finset.univ (fun k ↦ alphaZ k * m) * B) :
    (B : ℝ) ≤
      (6 * (((∑ k, alphaZ k) * m + 1 : ℕ) : ℝ)) ^ Fintype.card Coarse *
        Real.exp (
          (m : ℝ) * (((∑ i, gamma i : ℕ) : ℝ) * Real.log 2 *
            mme_modern_entropyBits
              (fun i ↦ (gamma i : ℝ) / ((∑ j, gamma j : ℕ) : ℝ))) -
          (m : ℝ) * (((∑ k, alphaZ k : ℕ) : ℝ) * Real.log 2 *
            mme_modern_entropyBits
              (fun k ↦ (alphaZ k : ℝ) / ((∑ l, alphaZ l : ℕ) : ℝ)))) := by
  let Eg : ℝ :=
    (m : ℝ) * (((∑ i, gamma i : ℕ) : ℝ) * Real.log 2 *
      mme_modern_entropyBits
        (fun i ↦ (gamma i : ℝ) / ((∑ j, gamma j : ℕ) : ℝ)))
  let Ea : ℝ :=
    (m : ℝ) * (((∑ k, alphaZ k : ℕ) : ℝ) * Real.log 2 *
      mme_modern_entropyBits
        (fun k ↦ (alphaZ k : ℝ) / ((∑ l, alphaZ l : ℕ) : ℝ)))
  let D : ℝ :=
    (6 * (((∑ k, alphaZ k) * m + 1 : ℕ) : ℝ)) ^ Fintype.card Coarse
  let Mg : ℝ := Nat.multinomial Finset.univ (fun i ↦ gamma i * m)
  let Ma : ℝ := Nat.multinomial Finset.univ (fun k ↦ alphaZ k * m)
  have hWa : 0 < ∑ k, alphaZ k := by omega
  have hgUpper : Mg ≤ Real.exp Eg := by
    dsimp [Mg, Eg]
    exact mme_dwz_multinomial_entropy_upper gamma m hm hW
  have haLower : Real.exp Ea ≤ D * Ma := by
    dsimp [Ea, D, Ma]
    exact mme_dwz_multinomial_entropy_polynomial_lower alphaZ m hm hWa
  have hfactorR : Mg = Ma * (B : ℝ) := by
    dsimp [Mg, Ma]
    exact_mod_cast hfactor
  have hD0 : 0 ≤ D := by
    dsimp [D]
    positivity
  change (B : ℝ) ≤ D * Real.exp (Eg - Ea)
  apply le_of_mul_le_mul_left _ (Real.exp_pos Ea)
  calc
    Real.exp Ea * (B : ℝ) ≤ (D * Ma) * (B : ℝ) := by
      gcongr
    _ = D * Mg := by rw [hfactorR]; ring
    _ ≤ D * Real.exp Eg := by gcongr
    _ = Real.exp Ea * (D * Real.exp (Eg - Ea)) := by
      rw [show Real.exp Ea * (D * Real.exp (Eg - Ea)) =
          D * (Real.exp Ea * Real.exp (Eg - Ea)) by ring]
      rw [← Real.exp_add]
      rw [show Ea + (Eg - Ea) = Eg by ring]

-- Prove2me | solution 1 for mme_dwz_square_repaired_standard_family_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:16:17.115973+00:00
-- url     : https://prove2.me/submissions/1aefbd79-09c1-4d20-89c0-bd7f641ddfb1

import Theorems.Thm_mme_dwz_square_repaired_standard_family_exact_hash_loss
import Theorems.Thm_mme_floor_behrend_polynomial_loss_ge_exp_sqrt

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ k : ℕ,
          TensorObj.Restrict
            (TensorObj.bigAdd
              (fun _ : Fin k => dwzTable2StandardObj K m))
            ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow
              (MME.DWZTable2Counts.scale * m)) ∧
          Real.rpow 2
                (retainedLogRate *
                  ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)) *
              Real.exp
                (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
            (k : ℝ) := by
  let B : ℝ := 32 * 6 ^ 20 * ((70 : ℕ).factorial : ℝ)
  let C : ℝ := 4 + 4 * ((16 : ℝ) + 1) + B
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C, B]
    positivity
  · filter_upwards
      [mme_dwz_square_repaired_standard_family_exact_hash_loss (K := K)]
      with m hm
    dsimp only at hm
    obtain ⟨k, p, D, hp, hpUpper, hDpos, hDUpper, hrestrict,
      hcount⟩ := hm
    refine ⟨k, hrestrict, ?_⟩
    have hloss :=
      mme_floor_behrend_polynomial_loss_ge_exp_sqrt
        (MME.DWZTable2Counts.scale * m) p D 16 B
        (by norm_num) hp hpUpper hDpos hDUpper
    have hrate :
        0 ≤ Real.rpow 2
          (retainedLogRate *
            ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    exact (mul_le_mul_of_nonneg_left hloss hrate).trans hcount

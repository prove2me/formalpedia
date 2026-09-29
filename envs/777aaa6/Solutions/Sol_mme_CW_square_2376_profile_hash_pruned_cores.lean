-- Prove2me | solution 1 for mme_CW_square_2376_profile_hash_pruned_cores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T15:58:25.61616+00:00
-- url     : https://prove2.me/submissions/d32cc644-cbeb-4363-a2d9-6beca0750233

import Theorems.Thm_mme_CW_2376_profile_rate_tendsto
import Theorems.Thm_mme_CW_square_2376_profile_finite_hash_certificate

open MME Filter

universe u

theorem solution
    {K : Type u} [Field K] :
    ∃ rate : ℕ → ℝ,
      Tendsto rate atTop (nhds 0) ∧
      (∀ m, 0 ≤ rate m) ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ s : ℕ,
          TensorObj.Restrict
            (TensorObj.bigAdd
              (fun _ : Fin s => cw2376ProfileCore K m))
            ((CWObj K 6).kronPow (6000000 * m)) ∧
          (cw2376ProfileCountBase * Real.exp (-(rate m))) ^
              (3000000 * m) ≤ (s : ℝ) := by
  exact ⟨cw2376ProfileRate,
    mme_CW_2376_profile_rate_tendsto.1,
    mme_CW_2376_profile_rate_tendsto.2,
    mme_CW_square_2376_profile_finite_hash_certificate (K := K)⟩

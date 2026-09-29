-- Prove2me | solution 1 for mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:14:39.921391+00:00
-- url     : https://prove2.me/submissions/00e6eae5-f2da-4a96-be5c-0fba05d315f5

import Theorems.Thm_mme_CW_q6_exact_coupled_address_regularity
import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss_of_regularity

open MME Filter Topology

theorem solution
    (L G : ℕ → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        let Zcount : ℕ :=
          Nat.choose (2 * N) (L N) *
            Nat.choose (2 * N - L N) (L N)
        let Xcount : ℕ := Nat.choose N (G N)
        let middle : ℕ := Nat.choose (2 * G N) (G N)
        (0 < L N ∧ L N + G N = N ∧ 341 * L N < 100 * G N) →
        ∃ A H : ℕ,
          ∃ _family : CWQ6PrimaryHashFamily N (L N) (G N) A H,
            H ≤ 4 ^ N ∧
            (Zcount : ℝ) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              (A : ℝ) ∧
            (middle : ℝ) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  apply mme_CW_q6_primary_hash_uniform_stars_sqrt_loss_of_regularity L G
  intro N hLG
  exact mme_CW_q6_exact_coupled_address_regularity N (L N) (G N) hLG

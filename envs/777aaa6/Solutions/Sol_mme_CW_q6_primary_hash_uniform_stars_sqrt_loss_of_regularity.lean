-- Prove2me | solution 1 for mme_CW_q6_primary_hash_uniform_stars_sqrt_loss_of_regularity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:30:47.206825+00:00
-- url     : https://prove2.me/submissions/11f9f65f-dcc3-4c80-9389-20be3d973fae

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_CW_q6_exact_address_incidence
import Theorems.Thm_mme_CW_q6_primary_hash_finite_AP_pruning_polynomial_loss
import Theorems.Thm_mme_CW_q6_behrend_half_modulus_factor_sqrt_loss

open MME Filter Topology

theorem solution
    (L G : ℕ → ℕ)
    (hregular : ∀ N : ℕ, L N + G N = N →
      CWQ6ExactAddressRegularity N (L N) (G N)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        let Zcount : ℕ :=
          Nat.choose (2 * N) (L N) *
            Nat.choose (2 * N - L N) (L N)
        let Xcount : ℕ := Nat.choose N (G N)
        let middle : ℕ := Nat.choose (2 * G N) (G N)
        (0 < L N ∧ L N + G N = N ∧ 341 * L N < 100 * G N) →
        ∃ A H : ℕ,
          ∃ family : CWQ6PrimaryHashFamily N (L N) (G N) A H,
            H ≤ 4 ^ N ∧
            (Zcount : ℝ) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              (A : ℝ) ∧
            (middle : ℝ) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  obtain ⟨d, hd, hfinite⟩ :=
    mme_CW_q6_primary_hash_finite_AP_pruning_polynomial_loss
  obtain ⟨C, hC, hbehrend⟩ :=
    mme_CW_q6_behrend_half_modulus_factor_sqrt_loss d
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbehrend] with N hbehrendN
  dsimp only
  intro hprofile
  have hGle : G N ≤ N := by omega
  obtain ⟨S, hSrange, hSfree, hSpos, hdensity⟩ :=
    hbehrendN (G N) hGle
  have hreg := hregular N hprofile.2.1
  obtain ⟨A, H, family, hH, hA, hmiddle⟩ :=
    hfinite N (L N) (G N) hreg hprofile S hSrange hSfree hSpos
  refine ⟨A, H, family, hH, ?_, ?_⟩
  · exact
      (mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg _)).trans hA
  · exact
      (mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg _)).trans
        hmiddle

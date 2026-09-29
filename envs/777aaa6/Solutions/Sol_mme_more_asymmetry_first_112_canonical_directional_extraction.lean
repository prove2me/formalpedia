-- Prove2me | solution 1 for mme_more_asymmetry_first_112_canonical_directional_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T22:46:29.829592+00:00
-- url     : https://prove2.me/submissions/5e9722a8-712e-4b84-9f3a-bc5d5d614f43

import Theorems.Thm_mme_more_asymmetry_first_112_canonical_family_certificate
import Theorems.Thm_mme_complete_split_112_first_slice_uniform_stars_sqrt_loss
import Theorems.Thm_mme_primary_hash_uniform_stars_joint_directional_capacity
import Mathlib.Tactic

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open scoped NNReal

universe u

set_option autoImplicit false
set_option warningAsError true

/-- The fixed released complete profile admits actual canonical-source
extractions on a cofinal sequence, with joint directional counts retained. -/
theorem solution :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ m : ℕ in atTop,
          let N : ℕ := 1180591620717411303424 * m
          let L : ℕ := 8959763742786037 * m
          let G : ℕ := 1180582660953668517387 * m
          let Zcount : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
          ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
            0 < A ∧ H ≤ 4 ^ N ∧
            (Zcount : ℝ) * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
            (Nat.choose (2 * N) N : ℝ) *
              Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
              4 * (A : ℝ) * (H : ℝ) ∧
            ∀ (K : Type u) [Field K] (epsilon : ℝ≥0),
              Nonempty
                (CTensorOneHOneFamilyCertificate
                  (restrictedCanonicalPower K 5 beta epsilon (2 * N))
                  A H (5 ^ (4 * G + 2 * L))) := by
  obtain ⟨beta, hbeta, hcertificate⟩ :=
    mme_more_asymmetry_first_112_canonical_family_certificate.{u}
  obtain ⟨C, hC, hfamilies⟩ :=
    mme_complete_split_112_first_slice_uniform_stars_sqrt_loss
  refine ⟨beta, hbeta, C, hC, ?_⟩
  filter_upwards [hfamilies] with m hm
  dsimp only at hm ⊢
  obtain ⟨A, H, family, hApos, hH, hA, hmiddle⟩ := hm
  have hLG : 8959763742786037 * m + 1180582660953668517387 * m =
      1180591620717411303424 * m := by omega
  have hcapacity := mme_primary_hash_uniform_stars_joint_directional_capacity
    (1180591620717411303424 * m) (8959763742786037 * m)
    (1180582660953668517387 * m) A H hLG C hA hmiddle
  refine ⟨A, H, family, hApos, hH, hA, hcapacity.2.2, ?_⟩
  intro K inst epsilon
  exact hcertificate K m A H family epsilon

-- Prove2me | solution 1 for mme_CW_primary_hash_Ctensor_outer_middle_certificates
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-07T14:49:31.694345+00:00
-- url     : https://prove2.me/submissions/6aee9958-8ce9-471f-abce-e0fed24b8918

import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
import Theorems.Thm_mme_CW_q6_primary_hash_sqrt_loss_absorption
import Theorems.Thm_mme_CW_coupled_three_grading_isomorphism_certificate
import Theorems.Thm_mme_coupled_four_block_induced_family_Ctensor_certificates_design

open MME Filter Topology

universe u

set_option autoImplicit false

/-- The hash family at the floor profile of a general `q`, with the
quarter-root loss substituted for the square-root loss. -/
theorem cert_induced_family_exists (q : ℕ) (tau : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((q : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let Zcount : ℕ :=
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      let Xcount : ℕ := Nat.choose N Gcount
      let middle : ℕ := Nat.choose (2 * Gcount) Gcount
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L Gcount A H,
        H ≤ 4 ^ N ∧
        (Zcount : ℝ) * Real.exp (-((N : ℝ) * loss / 12)) ≤
          (A : ℝ) ∧
        (middle : ℝ) * Real.exp (-((N : ℝ) * loss / 8)) ≤
          4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  let Lfun : ℕ → ℕ := fun N =>
    ⌊(2 / ((q : ℝ) ^ (3 * tau) + 2)) * (N : ℝ)⌋₊
  let Gfun : ℕ → ℕ := fun N => N - Lfun N
  obtain ⟨C, hC, hhash⟩ :=
    mme_CW_q6_primary_hash_uniform_stars_sqrt_loss Lfun Gfun
  have habsorb := mme_CW_q6_primary_hash_sqrt_loss_absorption C hC
  filter_upwards [hhash, habsorb] with N hhashN habsorbN
  dsimp only at hhashN habsorbN ⊢
  intro hprofile
  obtain ⟨A, H, family, hH, hA, hmiddle⟩ := hhashN hprofile
  refine ⟨A, H, family, hH, ?_, ?_⟩
  · exact
      (mul_le_mul_of_nonneg_left habsorbN.1 (Nat.cast_nonneg _)).trans hA
  · exact
      (mul_le_mul_of_nonneg_left habsorbN.2 (Nat.cast_nonneg _)).trans
        hmiddle

theorem solution
    {K : Type u} [Field K] (q : ℕ) (tau : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((q : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let Zcount : ℕ :=
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      let Xcount : ℕ := Nat.choose N Gcount
      let middle : ℕ := Nat.choose (2 * Gcount) Gcount
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∃ A H : ℕ,
        0 < H ∧
        H ≤ 4 ^ N ∧
        Nonempty
          (CTensorOneHOneFamilyCertificate
            ((coupledObj K q).kronPow (2 * N))
            A H (q ^ (4 * Gcount + 2 * L))) ∧
        (Zcount : ℝ) * Real.exp (-((N : ℝ) * loss / 12)) ≤
          (A : ℝ) ∧
        (middle : ℝ) * Real.exp (-((N : ℝ) * loss / 8)) ≤
          4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  filter_upwards [cert_induced_family_exists q tau] with N hN
  dsimp only at hN ⊢
  intro hprofile
  obtain ⟨A, H, family, hHle, hA, hmiddle⟩ := hN hprofile
  obtain ⟨grading, hSupport, h000, h111, h012, h102⟩ :=
    mme_CW_coupled_three_grading_isomorphism_certificate (K := K) q
  refine ⟨A, H, family.hHpos, hHle, ?_, hA, hmiddle⟩
  exact mme_coupled_four_block_induced_family_Ctensor_certificates_design
    q N
      ⌊2 / ((q : ℝ) ^ (3 * tau) + 2) * (N : ℝ)⌋₊
      (N - ⌊2 / ((q : ℝ) ^ (3 * tau) + 2) * (N : ℝ)⌋₊)
      A H (coupledObj K q) grading hSupport
      h000 h111 h012 h102 family

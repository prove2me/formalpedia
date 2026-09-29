-- Prove2me | solution 1 for mme_CW_q6_primary_hash_induced_family_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:15:15.357208+00:00
-- url     : https://prove2.me/submissions/e507ced5-a219-465f-b62d-4d8f03c61d2f

import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
import Theorems.Thm_mme_CW_q6_primary_hash_sqrt_loss_absorption

open MME Filter Topology

theorem solution
    (tau : ℝ) (_htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
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
    ⌊(2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ)⌋₊
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

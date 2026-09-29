-- Prove2me | solution 3 for rademacher_sampled_matrix_conditional_khintchine_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-22T00:25:11.786149+00:00
-- url     : https://prove2.me/submissions/03511c1a-2cbb-4a93-bebd-6f5b02c27f7d

import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_spectral_moment_le_schatten_moment_for_rademacher_sampled_matrix
import Theorems.Thm_rademacher_sampled_matrix_schatten_moment_khintchine_bound

open MatrixCompletion

/-
Reduction of `rademacher_sampled_matrix_conditional_khintchine_bound` (5584a87a) to
  * `spectral_moment_le_schatten_moment_for_rademacher_sampled_matrix` (72b5f655, Proved)
    — operator-norm q-moment ≤ Schatten-q-norm q-moment, and
  * `rademacher_sampled_matrix_schatten_moment_khintchine_bound` (d6e02cfd)
    — the Schatten-moment noncommutative Khintchine bound.

Source: Candès–Recht 2009 (arXiv:0805.4471), §6.1, the comparison
‖·‖_op ≤ ‖·‖_{S_q} composed with the noncommutative Khintchine inequality
(Lemma 6.1). The conditional spectral Khintchine RHS is the Schatten Khintchine RHS
after unfolding `rademacherSampledVarianceScale Ω p X = p⁻¹·√(max row/col energy)`.
-/

theorem solution :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              spectralNorm
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Ckh * Real.sqrt (q : ℝ) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            Real.sqrt
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X))) ^ q := by
  obtain ⟨Ckh, hCkh, hbound⟩ := rademacher_sampled_matrix_schatten_moment_khintchine_bound
  refine ⟨Ckh, hCkh, ?_⟩
  intro β hβ n₁ n₂ m q Omega X hq hqlog
  -- op-moment ≤ Schatten-moment
  have hople :
      rademacherExpectation
          (fun eps =>
            spectralNorm
              (rademacherSampledMatrix Omega eps
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
        rademacherExpectation
          (fun eps =>
            schattenNorm (q : ℝ)
              (rademacherSampledMatrix Omega eps
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) :=
    spectral_moment_le_schatten_moment_for_rademacher_sampled_matrix β hβ n₁ n₂ m q Omega X hq hqlog
  -- Schatten Khintchine bound
  have hkh :
      rademacherExpectation
          (fun eps =>
            schattenNorm (q : ℝ)
              (rademacherSampledMatrix Omega eps
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
        (Ckh * Real.sqrt (q : ℝ) *
          rademacherSampledVarianceScale Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q :=
    hbound β hβ n₁ n₂ m q Omega X hq hqlog
  -- the two RHS forms are equal after unfolding `rademacherSampledVarianceScale`
  have heq :
      (Ckh * Real.sqrt (q : ℝ) *
          rademacherSampledVarianceScale Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q =
        (Ckh * Real.sqrt (q : ℝ) *
          (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
          Real.sqrt
            (max (sampledRowEnergyMax Omega X)
              (sampledColumnEnergyMax Omega X))) ^ q := by
    unfold rademacherSampledVarianceScale
    ring_nf
  rw [← heq]
  exact le_trans hople hkh

-- Prove2me | solution 1 for rademacher_sampled_matrix_schatten_moment_khintchine_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T19:52:31.918561+00:00
-- url     : https://prove2.me/submissions/4309a6a1-bc4f-4326-ac31-50ba8ae55080

import Theorems.Thm_rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale
import Theorems.Thm_rademacher_sampled_matrix_schatten_moment_khintchine_low_q_boundary

open MatrixCompletion

/-- Source: Candes-Recht 2008, Section 6.1, Lemma 6.1, p. 24.

Lemma 6.1 is a noncommutative Khintchine inequality for `q ≥ 2`.  The uploaded
parent theorem was stated with `1 ≤ q`, so the correct reduction is a case
split: the source branch proves the theorem for `q ≥ 2`, and a separate formal
boundary lemma handles the only remaining `q = 1`/small-dimension corner.
Both children expose monotone constants; the parent uses their maximum. -/
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
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Ckh * Real.sqrt (q : ℝ) *
            rademacherSampledVarianceScale Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q := by
  rcases rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale with
    ⟨Ctwo, hCtwo, hTwo⟩
  rcases rademacher_sampled_matrix_schatten_moment_khintchine_low_q_boundary with
    ⟨Clow, hClow, hLow⟩
  refine ⟨max Ctwo Clow, lt_of_lt_of_le hCtwo (le_max_left Ctwo Clow), ?_⟩
  intro β hβ n₁ n₂ m q Omega X hqOne hqlog
  by_cases hqTwo : 2 ≤ q
  · exact hTwo (max Ctwo Clow) (le_max_left Ctwo Clow)
      β hβ n₁ n₂ m q Omega X hqTwo hqlog
  · exact hLow (max Ctwo Clow) (le_max_right Ctwo Clow)
      β hβ n₁ n₂ m q Omega X hqOne hqTwo hqlog


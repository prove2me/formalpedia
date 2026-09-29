-- Prove2me | solution 2 for rademacher_sampled_matrix_conditional_khintchine_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T14:34:19.651878+00:00
-- url     : https://prove2.me/submissions/716b618b-7351-44b4-8807-8fef23ec25d7

import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_rademacher_sampled_matrix_schatten_moment_khintchine_bound
import Theorems.Thm_rademacher_expectation_monotone
import Theorems.Thm_spectral_norm_le_schatten_norm
import Mathlib.Analysis.SpecialFunctions.Sqrt
open MatrixCompletion
open scoped Classical BigOperators

/-- Conditional Khintchine bound for the operator norm follows from the
Schatten-`q`-moment bound: pointwise `‖R‖_op ≤ ‖R‖_{S_q}` (since `q ≥ 1`),
raised to the `q`-th power (both nonnegative), then monotonicity of the
Rademacher expectation, chained with the Schatten moment bound.  The variance
scale `rademacherSampledVarianceScale = p⁻¹ √(max energies)` is precisely the
right-hand factor here, so the constant `Ckh` carries over unchanged. -/
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
  obtain ⟨Ckh, hCkh, hbound⟩ :=
    rademacher_sampled_matrix_schatten_moment_khintchine_bound
  refine ⟨Ckh, hCkh, ?_⟩
  intro β hβ n₁ n₂ m q Omega X hq1 hqlb
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  -- Pointwise: ‖R‖_op^q ≤ ‖R‖_{S_q}^q
  have hpt : ∀ eps : Finset (Fin n₁ × Fin n₂),
      spectralNorm (rademacherSampledMatrix Omega eps p X) ^ q ≤
        schattenNorm (q : ℝ) (rademacherSampledMatrix Omega eps p X) ^ q := by
    intro eps
    apply pow_le_pow_left₀
    · -- spectralNorm ≥ 0
      unfold spectralNorm
      exact norm_nonneg _
    · exact spectral_norm_le_schatten_norm q _ hq1
  -- Monotonicity of the Rademacher expectation
  have hmono :
      rademacherExpectation
          (fun eps =>
            spectralNorm (rademacherSampledMatrix Omega eps p X) ^ q) ≤
        rademacherExpectation
          (fun eps =>
            schattenNorm (q : ℝ) (rademacherSampledMatrix Omega eps p X) ^ q) :=
    rademacher_expectation_monotone _ _ hpt
  -- Chain with the Schatten moment bound
  refine le_trans hmono ?_
  have hb := hbound β hβ n₁ n₂ m q Omega X hq1 hqlb
  -- The Schatten bound's RHS equals our RHS (varScale = p⁻¹√(max energies)).
  rw [hp]
  convert hb using 2
  unfold rademacherSampledVarianceScale
  ring

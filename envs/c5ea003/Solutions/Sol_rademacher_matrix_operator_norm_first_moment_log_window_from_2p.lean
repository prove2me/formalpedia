-- Prove2me | solution 1 for rademacher_matrix_operator_norm_first_moment_log_window_from_2p
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-25T20:25:23.874868+00:00
-- url     : https://prove2.me/submissions/f133f114-b44c-4dd7-878e-bfa976eb9497

import Theorems.Thm_rademacher_matrix_operator_norm_2p_moment_bound
import Theorems.Thm_finite_rademacher_weighted_first_moment_le_even_moment_root
import Theorems.Thm_matrix_khintchine_log_window_dimension_factor
import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Matrix MatrixCompletion
open scoped Classical BigOperators Matrix

theorem solution :
    ∃ Clog : ℝ, 0 < Clog ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
        {d N : ℕ}, 0 < d → 2 ≤ N → d ≤ N * N →
        ∀ (H : ι → Matrix (Fin d) (Fin d) ℝ),
        (∀ c, (H c).IsHermitian) →
        ∀ (normV : ℝ), 0 ≤ normV →
        (hVHerm : (∑ c : ι, H c * H c).IsHermitian) →
        (∀ i, hVHerm.eigenvalues i ≤ normV) →
        (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
          spectralNorm (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c))
        ≤ Clog * Real.sqrt (Real.log (N : ℝ)) * Real.sqrt normV := by
  rcases matrix_khintchine_log_window_dimension_factor with
    ⟨Cwin, hCwin_pos, hCwin⟩
  refine ⟨Cwin, hCwin_pos, ?_⟩
  intro ι _ _ d N hd hN hdN H hHerm normV hnormVnn hVHerm hnormV
  let F : Finset ι → ℝ := fun eps =>
    spectralNorm (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c)
  have hF_nonneg : ∀ eps, 0 ≤ F eps := by
    intro eps
    dsimp [F, spectralNorm]
    exact norm_nonneg _
  rcases hCwin hd hN hdN with ⟨p, hp, hfactor⟩
  have hfirst :=
    finite_rademacher_weighted_first_moment_le_even_moment_root F hF_nonneg p hp
  have hmoment :=
    rademacher_matrix_operator_norm_2p_moment_bound
      hd H hHerm normV hnormVnn hVHerm hnormV p hp
  have hsqrt_nonneg : 0 ≤ Real.sqrt normV := Real.sqrt_nonneg _
  have hmul_factor :=
    mul_le_mul_of_nonneg_right hfactor hsqrt_nonneg
  have hscalar :
      Real.sqrt (2 * p) * Real.sqrt normV *
          (d : ℝ) ^ ((1 : ℝ) / (2 * p)) ≤
        Cwin * Real.sqrt (Real.log (N : ℝ)) * Real.sqrt normV := by
    calc
      Real.sqrt (2 * p) * Real.sqrt normV *
          (d : ℝ) ^ ((1 : ℝ) / (2 * p))
          = (Real.sqrt (2 * (p : ℝ)) *
              (d : ℝ) ^ ((1 : ℝ) / (2 * (p : ℝ)))) *
              Real.sqrt normV := by ring
      _ ≤ (Cwin * Real.sqrt (Real.log (N : ℝ))) * Real.sqrt normV := hmul_factor
      _ = Cwin * Real.sqrt (Real.log (N : ℝ)) * Real.sqrt normV := by ring
  calc
    (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
        spectralNorm (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c))
        ≤ (∑ eps : Finset ι,
            ((1 : ℝ) / 2) ^ (Fintype.card ι) *
              (spectralNorm
                (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c)) ^ (2 * p))
            ^ ((1 : ℝ) / (2 * p)) := by
          simpa [F] using hfirst
    _ ≤ Real.sqrt (2 * p) * Real.sqrt normV *
          (d : ℝ) ^ ((1 : ℝ) / (2 * p)) := hmoment
    _ ≤ Cwin * Real.sqrt (Real.log (N : ℝ)) * Real.sqrt normV := hscalar


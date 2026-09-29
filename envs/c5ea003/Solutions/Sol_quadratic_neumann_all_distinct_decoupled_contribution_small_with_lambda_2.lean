-- Prove2me | solution 2 for quadratic_neumann_all_distinct_decoupled_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-04T14:24:02.710183+00:00
-- url     : https://prove2.me/submissions/c783e8d4-d028-48ac-b7f9-2d39ff287aad

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_quadratic_neumann_all_distinct_middle_coefficient_entry_sup_pair_event_honest_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_outer_coefficient_entry_bound_from_middle_nonempty
import Theorems.Thm_quadratic_neumann_all_distinct_decoupled_as_outer_centered_fluctuation
import Theorems.Thm_quadratic_neumann_all_distinct_outer_decoupled_threshold_from_honest_coefficient_scale
import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_quadratic_neumann_sample_lower_implies_fixed_matrix_sample_lower
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_bernoulli_triple_event_probability_from_pair_marginal_and_conditional_lower_bounds_of_nonneg
import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a0_geom_dim
import Mathlib.Data.Fintype.Order

open MatrixCompletion

/-- 5157715d: direct closure of the triple-decoupled all-distinct quadratic
contribution (Candès–Recht §6.3, case 5), bypassing the unprovable
dimensionless drift node `..._decoupled_from_middle_coefficient_bound`:

* the Proved HONEST pair event (`fdc5c40c`, at `μ₁ := μ₀√r` via the A0
  geometric-mean bridge) carries the full nested-Bernstein dimensional scale
  for the middle coefficients on `(Ω₂,Ω₃)`;
* the outer coefficient matrix entries inherit that bound (`1b3411e9`);
* Theorem 6.3 (`fixed_matrix_centered_sampling_spectral_bound`) controls the
  outer centered sampling over `Ω₁`, and the new honest threshold node
  absorbs `√(βNlogN/p) ×` honest scale into `Cth·λ^{-3/2}` — the tight case,
  the dimensional factors cancel exactly;
* the identity `decoupled = csf(Ω₁, outer)` (`2c1a1db1`) and the generic
  triple-event assembler (`ea982007`) land the triple event. -/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliTripleEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                C * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Ccoef, ccoef, hCcoef0, hccoef0, hcoef⟩ :=
    quadratic_neumann_all_distinct_middle_coefficient_entry_sup_pair_event_honest_min_dim
  obtain ⟨Cfix, hCfix0, hfix⟩ := fixed_matrix_centered_sampling_spectral_bound
  obtain ⟨Cth, hCth0, hth⟩ :=
    quadratic_neumann_all_distinct_outer_decoupled_threshold_from_honest_coefficient_scale
      Cfix Ccoef hCfix0 hCcoef0
  refine ⟨Cth, 1 + ccoef, hCth0, by linarith, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsample
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hrR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrR0 : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le one_pos hrR1
  have hμ₀0 : (0 : ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hN0 : (0 : ℝ) < (↑(max n₁ n₂) : ℝ) := by
    have h := lt_of_lt_of_le hn₁ (le_max_left n₁ n₂)
    exact_mod_cast h
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  -- μ₁ := μ₀·√r is a legal A1 parameter, by the A0 geometric-mean bridge
  have hsr1 : (1 : ℝ) ≤ Real.sqrt (r : ℝ) := Real.one_le_sqrt.mpr hrR1
  have hμ₁' : (1 : ℝ) ≤ μ₀ * Real.sqrt (r : ℝ) := by
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ μ₀ * Real.sqrt (r : ℝ) :=
          mul_le_mul hμ₀ hsr1 zero_le_one (le_trans zero_le_one hμ₀)
  have hA1' : A1 S (μ₀ * Real.sqrt (r : ℝ)) := by
    have hsup := entry_sup_norm_sign_matrix_bound_from_a0_geom_dim
      n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
    have hmulself : Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ) = (r : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hrR0)
    have halg : (μ₀ * Real.sqrt (r : ℝ)) *
        (Real.sqrt (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) =
        μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) := by
      rw [show (μ₀ * Real.sqrt (r : ℝ)) *
          (Real.sqrt (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) =
          μ₀ * (Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ)) /
            Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) from by ring,
        hmulself]
    intro i j
    have hij : |signMatrix S i j| ≤ entrySupNorm (signMatrix S) := by
      have h1 : |signMatrix S i j| ≤ ⨆ j' : Fin n₂, |signMatrix S i j'| :=
        Finite.le_ciSup (f := fun j' : Fin n₂ => |signMatrix S i j'|) j
      have h2 : (⨆ j' : Fin n₂, |signMatrix S i j'|) ≤
          ⨆ i' : Fin n₁, ⨆ j' : Fin n₂, |signMatrix S i' j'| :=
        Finite.le_ciSup
          (f := fun i' : Fin n₁ => ⨆ j' : Fin n₂, |signMatrix S i' j'|) i
      calc |signMatrix S i j| ≤ ⨆ j' : Fin n₂, |signMatrix S i j'| := h1
        _ ≤ ⨆ i' : Fin n₁, ⨆ j' : Fin n₂, |signMatrix S i' j'| := h2
        _ = entrySupNorm (signMatrix S) := rfl
    calc |signMatrix S i j|
        ≤ entrySupNorm (signMatrix S) := hij
      _ ≤ μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) := hsup
      _ = (μ₀ * Real.sqrt (r : ℝ)) *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
          rw [Real.sqrt_div (le_of_lt hrR0)]
          exact halg.symm
  -- marginal: the honest pair event on (Ω₂,Ω₃) at μ₁ := μ₀·√r
  have hpair := hcoef β hβ n₁ n₂ r m M μ₀ (μ₀ * Real.sqrt (r : ℝ)) S
    hn₁ hn₂ hr hm hμ₀ hμ₁' hA0 hA1'
  -- Theorem 6.3's sample hypothesis
  have hmfix : (m : ℝ) ≥
      β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) :=
    quadratic_neumann_sample_lower_implies_fixed_matrix_sample_lower
      β lam n₁ n₂ r m μ₀ hβ hlam hn₁ hn₂ hr hμ₀ hsample
  -- conditional: Theorem 6.3 on the outer coefficient matrix + threshold
  have hcond : ∀ Omega2 Omega3 : Finset (Fin n₁ × Fin n₂),
      QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
        (Ccoef *
          (Real.sqrt
                (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
              (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                (Real.sqrt
                      (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
                    (μ₀ * Real.sqrt (r : ℝ) *
                      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                  (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
                    (μ₀ * Real.sqrt (r : ℝ) *
                      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) +
            (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
              ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                (Real.sqrt
                      (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
                    (μ₀ * Real.sqrt (r : ℝ) *
                      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                  (((β + 4) * Real.log (↑(max n₁ n₂))) / p) *
                    (μ₀ * Real.sqrt (r : ℝ) *
                      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))))) →
      bernoulliEventProb p
          (fun Omega1 =>
            spectralNorm
              (quadraticNeumannAllDistinctDecoupledContribution
                Omega1 Omega2 Omega3 S p) ≤
              Cth * Real.rpow lam (-((3 : ℝ) / 2))) ≥
        1 - 1 * Real.rpow (↑(max n₁ n₂)) (-β) := by
    intro Omega2 Omega3 hmid
    have hB := quadratic_neumann_all_distinct_outer_coefficient_entry_bound_from_middle_nonempty
      Omega2 Omega3 S p _ hn₁ hn₂ hmid
    have h63 := hfix β hβ n₁ n₂ m
      (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p)
      hn₁ hn₂ hm hmfix
    have himp : ∀ Omega1 : Finset (Fin n₁ × Fin n₂),
        CenteredSamplingSpectralBound Omega1 p
          (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p)
          (Cfix * Real.sqrt
            ((β * (↑(max n₁ n₂)) *
                Real.log (↑(max n₁ n₂))) / p) *
            entrySupNorm
              (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p)) →
        spectralNorm
          (quadraticNeumannAllDistinctDecoupledContribution
            Omega1 Omega2 Omega3 S p) ≤
          Cth * Real.rpow lam (-((3 : ℝ) / 2)) := by
      intro Omega1 hev
      exact hth β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hsample Omega1
        (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p)
        (quadraticNeumannAllDistinctDecoupledContribution
          Omega1 Omega2 Omega3 S p)
        (quadratic_neumann_all_distinct_decoupled_as_outer_centered_fluctuation
          Omega1 Omega2 Omega3 S p)
        hB hev
    have hmono := bernoulli_event_probability_mono p
      (fun Omega1 =>
        CenteredSamplingSpectralBound Omega1 p
          (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p)
          (Cfix * Real.sqrt
            ((β * (↑(max n₁ n₂)) *
                Real.log (↑(max n₁ n₂))) / p) *
            entrySupNorm
              (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p)))
      (fun Omega1 =>
        spectralNorm
          (quadraticNeumannAllDistinctDecoupledContribution
            Omega1 Omega2 Omega3 S p) ≤
          Cth * Real.rpow lam (-((3 : ℝ) / 2)))
      hp0 hp1 himp
    exact le_trans h63 hmono
  -- triple event via the generic Bernoulli triple assembler
  have hcondscale : (0 : ℝ) ≤ 1 * Real.rpow (↑(max n₁ n₂)) (-β) := by
    rw [one_mul]
    exact le_of_lt (Real.rpow_pos_of_pos hN0 (-β))
  have htriple :=
    bernoulli_triple_event_probability_from_pair_marginal_and_conditional_lower_bounds_of_nonneg
      p ccoef 1 (Real.rpow (↑(max n₁ n₂)) (-β)) _ _
      hp0 hp1 hcondscale hpair hcond
  exact htriple

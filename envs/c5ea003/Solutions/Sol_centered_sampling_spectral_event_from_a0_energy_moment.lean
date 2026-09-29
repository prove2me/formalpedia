-- Prove2me | solution 1 for centered_sampling_spectral_event_from_a0_energy_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-01T09:16:32.898583+00:00
-- url     : https://prove2.me/submissions/1face284-08a0-4e25-aaf2-4ac61df436bd

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_centered_sampling_spectral_event_from_energy_moment
import Theorems.Thm_bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

/-!
# node (iv), UNIFORM-`Cenergy` form (soundness witness for the strengthened stub)

Source: Candès--Recht 2008, PDF p. 26, Theorem 6.3 and equation (6.7),
combined with the row/column sampled-energy estimates used in Section 6.3,
PDF pp. 31--32 around equation (6.20).

Identical to `Sol_centered_sampling_spectral_event_from_a0_energy_moment` except
the energy-moment constant `Cenergy` is exposed as a second GLOBAL existential
(it is obtained once from the Proved
`bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN`, so it is
genuinely uniform in the instance and in `X`).  This is the interface brick 1
needs to obtain a uniform pair constant.
-/

theorem solution :
    ∃ Ctail Cenergy : ℝ, 0 < Ctail ∧ 0 < Cenergy ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) →
        2 ≤ max n₁ n₂ →
        ∃ (q : ℕ),
          1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                CenteredSamplingSpectralBound Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                  (Ctail * Real.sqrt (q : ℝ) *
                    (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
                    Real.sqrt
                      (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (↑(max n₁ n₂)) * entrySupNorm X ^ 2))) ≥
            1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Ctail, hCtail, hEvent⟩ :=
    centered_sampling_spectral_event_from_energy_moment
  obtain ⟨Cenergy, hCenergy, hEnergyMoment⟩ :=
    bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN
  refine ⟨Ctail, Cenergy, hCtail, hCenergy, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hSample hmax2
  obtain ⟨q, hq1, hqLog, hqUpper, _hq2pN, hmoment⟩ :=
    hEnergyMoment β hβ n₁ n₂ m X hn₁ hn₂ hm hSample hmax2
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN_def
  set EnergyBound : ℝ := Cenergy * p * N * entrySupNorm X ^ 2 with hEB_def
  have hp_nonneg : 0 ≤ p := by rw [hp_def]; positivity
  have hN_nonneg : 0 ≤ N := by rw [hN_def]; positivity
  have hEB_nonneg : 0 ≤ EnergyBound := by
    rw [hEB_def]
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCenergy) hp_nonneg) hN_nonneg)
      (sq_nonneg _)
  have hMomentEB :
      bernoulliExpectation p
          (fun Omega =>
            (max (sampledRowEnergyMax Omega X)
              (sampledColumnEnergyMax Omega X)) ^ q) ≤ EnergyBound ^ q := hmoment
  have hEvt := hEvent β hβ n₁ n₂ m q X EnergyBound hn₁ hn₂ hm hq1 hqLog hSample
    hEB_nonneg hMomentEB
  refine ⟨q, hq1, hqLog, hqUpper, ?_⟩
  rw [← hp_def, ← hN_def] at hEvt
  -- fold EnergyBound to the explicit form in the goal
  have : EnergyBound = Cenergy * p * N * entrySupNorm X ^ 2 := hEB_def
  rw [hEB_def] at hEvt
  exact hEvt

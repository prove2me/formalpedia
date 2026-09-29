-- Prove2me | Theorems.Thm_centered_sampling_spectral_event_from_energy_moment
-- name    : centered_sampling_spectral_event_from_energy_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-01T09:14:33.757633+00:00
-- url     : https://prove2.me/theorems/ecbec164-8d43-417b-9f02-f324324aa628
-- statement:
--   Tight row/column-energy Theorem-6.3 spectral EVENT keystone (energy-MOMENT
--   form).  Takes the probabilistic energy `q`-moment
--   `bExp[max(rowEnergy,colEnergy)^q] ≤ EnergyBound^q` and delivers the centered
--   sampling spectral event at the tight Lemma-6.6 scale
--   `Ctail·√q·p⁻¹·√EnergyBound`.  Proved in
--   `Solutions/Sol_centered_sampling_spectral_event_from_energy_moment.lean`.
--
--   Source: Candès--Recht 2008, PDF p. 26, Theorem 6.3 and equation (6.7),
--   with the energy-moment interface supplying the row/column scale used later in
--   Section 6.3.
-- source:
--   Candès--Recht 2008, Exact Matrix Completion via Convex Optimization, PDF pp. 26 and 28--32, Theorem 6.3 (eq. 6.7), Lemma 6.6 (eqs. 6.15--6.17), Lemma 6.7 (eq. 6.19), and Section 6.3 around eqs. 6.20--6.21.

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_rademacher
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

/-- Tight row/column-energy Theorem-6.3 spectral EVENT keystone (energy-MOMENT
form).  Takes the probabilistic energy `q`-moment
`bExp[max(rowEnergy,colEnergy)^q] ≤ EnergyBound^q` and delivers the centered
sampling spectral event at the tight Lemma-6.6 scale
`Ctail·√q·p⁻¹·√EnergyBound`.  Proved in
`Solutions/Sol_centered_sampling_spectral_event_from_energy_moment.lean`.

Source: Candès--Recht 2008, PDF p. 26, Theorem 6.3 and equation (6.7),
with the energy-moment interface supplying the row/column scale used later in
Section 6.3. -/
theorem centered_sampling_spectral_event_from_energy_moment :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) (EnergyBound : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) →
        0 ≤ EnergyBound →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X)) ^ q) ≤ EnergyBound ^ q →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                (Ctail * Real.sqrt (q : ℝ) *
                  (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
                  Real.sqrt EnergyBound)) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry

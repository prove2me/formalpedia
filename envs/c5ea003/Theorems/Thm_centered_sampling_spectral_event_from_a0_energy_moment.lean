-- Prove2me | Theorems.Thm_centered_sampling_spectral_event_from_a0_energy_moment
-- name    : centered_sampling_spectral_event_from_a0_energy_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-01T09:16:29.541745+00:00
-- url     : https://prove2.me/theorems/1d424ee2-6b63-4002-898a-319de0df4b41
-- statement:
--   Tight centered-sampling spectral EVENT via the closed per-row binomial energy
--   moment (node (iv)).  For a fixed matrix `X` with the general sample lower bound
--   `m ≥ β·N·log N` and `2 ≤ max n₁ n₂`, it produces an admissible exponent `q`
--   (`q ≥ β log N`, `q ≤ 2β log N`) and the probabilistic energy bound
--   `EnergyBound = Cenergy·p·N·‖X‖∞²` (with a UNIFORM constant `Cenergy`, independent
--   of the instance and of `X`), together with the centered spectral event at the
--   tight Lemma-6.6 threshold `Ctail·√q·p⁻¹·√EnergyBound`.
--
--   Source: Candès–Recht 2008, §6.3, PDF pp. 31--32, Lemma 6.6 / Lemma 6.2.
-- source:
--   Candès--Recht 2008, Exact Matrix Completion via Convex Optimization, PDF pp. 26 and 28--32, Theorem 6.3 (eq. 6.7), Lemma 6.6 (eqs. 6.15--6.17), Lemma 6.7 (eq. 6.19), and Section 6.3 around eqs. 6.20--6.21.

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_rademacher

open MatrixCompletion

open scoped Classical BigOperators

/-- Tight centered-sampling spectral EVENT via the closed per-row binomial energy
moment (node (iv)).  For a fixed matrix `X` with the general sample lower bound
`m ≥ β·N·log N` and `2 ≤ max n₁ n₂`, it produces an admissible exponent `q`
(`q ≥ β log N`, `q ≤ 2β log N`) and the probabilistic energy bound
`EnergyBound = Cenergy·p·N·‖X‖∞²` (with a UNIFORM constant `Cenergy`, independent
of the instance and of `X`), together with the centered spectral event at the
tight Lemma-6.6 threshold `Ctail·√q·p⁻¹·√EnergyBound`.

Source: Candès–Recht 2008, §6.3, PDF pp. 31--32, Lemma 6.6 / Lemma 6.2. -/
theorem centered_sampling_spectral_event_from_a0_energy_moment :
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
            1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry

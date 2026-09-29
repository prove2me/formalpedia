-- Prove2me | solution 1 for bernoulli_sampled_row_energy_moment_from_count_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T04:47:47.696186+00:00
-- url     : https://prove2.me/submissions/cc0fa5dd-b5ef-4d15-b44d-daa3ecd6d0c1

import Theorems.Thm_bernoulli_sampled_row_energy_moment_from_count_moment
import Theorems.Thm_bernoulli_energy_moment_from_count_moment_and_pointwise_domination
import Theorems.Thm_sampled_row_energy_max_nonnegative
import Theorems.Thm_sampled_row_count_max_nonnegative

open MatrixCompletion

/-- Specialize the generic energy/count moment comparison to sampled row
energies and sampled row counts. -/
theorem solution
    (Ccount : ℝ) :
    0 < Ccount →
    ∃ Crow : ℝ, 0 < Crow ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂)) →
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          sampledRowEnergyMax Omega X ≤
            entrySupNorm X ^ 2 * sampledRowCountMax Omega) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega : Finset (Fin n₁ × Fin n₂) =>
              sampledRowCountMax Omega ^ q) ≤
          (Ccount * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega => sampledRowEnergyMax Omega X ^ q) ≤
          (Crow * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
  intro hCcount
  rcases bernoulli_energy_moment_from_count_moment_and_pointwise_domination
      Ccount hCcount with
    ⟨Cenergy, hCenergy, hEnergy⟩
  refine ⟨Cenergy, hCenergy, ?_⟩
  intro β hβ n₁ n₂ m q X hn₁ hn₂ hm hqOne hqLog hqUpper
    hPointwise hCount
  exact hEnergy β hβ n₁ n₂ m q X hn₁ hn₂ hm hqOne hqLog hqUpper
    (fun Omega => sampledRowEnergyMax Omega X)
    (fun Omega => sampledRowCountMax Omega)
    (fun Omega => sampled_row_energy_max_nonnegative Omega X)
    (fun Omega => sampled_row_count_max_nonnegative Omega)
    hPointwise hCount


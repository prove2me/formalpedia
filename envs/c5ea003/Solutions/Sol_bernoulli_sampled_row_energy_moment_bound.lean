-- Prove2me | solution 1 for bernoulli_sampled_row_energy_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:40.947058+00:00
-- url     : https://prove2.me/submissions/ea08725b-495c-4876-b682-72700e4c8658

import Theorems.Thm_sampled_row_energy_max_le_entry_sup_norm_sq_mul_row_count_max
import Theorems.Thm_bernoulli_sampled_row_count_max_moment_bound
import Theorems.Thm_bernoulli_sampled_row_energy_moment_from_count_moment

open MatrixCompletion

/-- Prove the row-energy half of Lemma 6.2 by reducing sampled row energies to
sampled row counts, applying the binomial maximum-count moment estimate, and
absorbing the `||X||_∞²` factor. -/
theorem solution :
    ∃ Crow : ℝ, 0 < Crow ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega => sampledRowEnergyMax Omega X ^ q) ≤
          (Crow * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
  rcases bernoulli_sampled_row_count_max_moment_bound with
    ⟨Ccount, hCcount, hCount⟩
  rcases bernoulli_sampled_row_energy_moment_from_count_moment
      Ccount hCcount with
    ⟨Crow, hCrow, hEnergy⟩
  refine ⟨Crow, hCrow, ?_⟩
  intro β hβ n₁ n₂ m q X hn₁ hn₂ hm hqOne hqLog hqUpper
  have hPointwise :
      ∀ Omega : Finset (Fin n₁ × Fin n₂),
        sampledRowEnergyMax Omega X ≤
          entrySupNorm X ^ 2 * sampledRowCountMax Omega := by
    intro Omega
    exact sampled_row_energy_max_le_entry_sup_norm_sq_mul_row_count_max
      Omega X
  have hCountBound :=
    hCount β hβ n₁ n₂ m q hn₁ hn₂ hm hqOne hqLog hqUpper
  exact hEnergy β hβ n₁ n₂ m q X hn₁ hn₂ hm hqOne hqLog
    hqUpper hPointwise hCountBound


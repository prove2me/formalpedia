-- Prove2me | solution 1 for bernoulli_sampled_column_energy_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:38.739038+00:00
-- url     : https://prove2.me/submissions/d4ed8985-3763-408d-8448-34c52e1924ea

import Theorems.Thm_sampled_column_energy_max_le_entry_sup_norm_sq_mul_column_count_max
import Theorems.Thm_bernoulli_sampled_column_count_max_moment_bound
import Theorems.Thm_bernoulli_sampled_column_energy_moment_from_count_moment

open MatrixCompletion

/-- Prove the column-energy half of Lemma 6.2 by reducing sampled column
energies to sampled column counts, applying the binomial maximum-count moment
estimate, and absorbing the `||X||_∞²` factor. -/
theorem solution :
    ∃ Ccol : ℝ, 0 < Ccol ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega => sampledColumnEnergyMax Omega X ^ q) ≤
          (Ccol * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
  rcases bernoulli_sampled_column_count_max_moment_bound with
    ⟨Ccount, hCcount, hCount⟩
  rcases bernoulli_sampled_column_energy_moment_from_count_moment
      Ccount hCcount with
    ⟨Ccol, hCcol, hEnergy⟩
  refine ⟨Ccol, hCcol, ?_⟩
  intro β hβ n₁ n₂ m q X hn₁ hn₂ hm hqOne hqLog hqUpper
  have hPointwise :
      ∀ Omega : Finset (Fin n₁ × Fin n₂),
        sampledColumnEnergyMax Omega X ≤
          entrySupNorm X ^ 2 * sampledColumnCountMax Omega := by
    intro Omega
    exact sampled_column_energy_max_le_entry_sup_norm_sq_mul_column_count_max
      Omega X
  have hCountBound :=
    hCount β hβ n₁ n₂ m q hn₁ hn₂ hm hqOne hqLog hqUpper
  exact hEnergy β hβ n₁ n₂ m q X hn₁ hn₂ hm hqOne hqLog
    hqUpper hPointwise hCountBound


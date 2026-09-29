-- Prove2me | Theorems.Thm_centered_sampling_log_moment_from_row_column_energy_2pN
-- name    : centered_sampling_log_moment_from_row_column_energy_2pN
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-25T06:28:16.372568+00:00
-- url     : https://prove2.me/theorems/a95b20ce-a16f-44e1-bf10-9ccc1aa7b747
-- statement:
--   `_2pN` variant of the Candes-Recht Section 6.1 noncommutative-Khintchine conversion. Given a universal energy constant $C_{energy}>0$ and the row/column sampled-energy log-moment estimate at the RELAXED exponent window $q\le 2pN$ (instead of the strict $q\le pN$), there is a universal constant $C_{moment}>0$ such that for all $\beta>2$, dimensions, and sampling, the Bernoulli $q$-th moment of the spectral norm of the centered sampling fluctuation is at most $(C_{moment}\sqrt{\beta N\log N/p}\,\lVert X\rVert_\infty)^q$. The relaxed window is exactly the one supplied by the one-sample lower bound at $q=\lceil\beta\log N\rceil$; the window hypothesis is dead weight in the Khintchine conversion itself.
-- source:
--   Candes-Recht 2008 (arXiv:0805.4471) Section 6.1, eq (6.5)-(6.6), Lemma 6.1

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem centered_sampling_log_moment_from_row_column_energy_2pN
    (Cenergy : ℝ) :
    0 < Cenergy →
    ∃ Cmoment : ℝ, 0 < Cmoment ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        (∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
          (q : ℝ) ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂))) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X)) ^ q) ≤
            (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q) →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                spectralNorm
                  (centeredSamplingFluctuation Omega
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
            (Cmoment * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) ^ q := by
  sorry

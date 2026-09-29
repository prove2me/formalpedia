-- Prove2me | Theorems.Thm_bernoulli_sampled_row_column_energy_controlled_log_moment_bound_of_two_sample_lower
-- name    : bernoulli_sampled_row_column_energy_controlled_log_moment_bound_of_two_sample_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T08:16:50.687461+00:00
-- url     : https://prove2.me/theorems/5e44011f-faa4-47d0-8ae1-0083eea7a3ce
-- statement:
--   This is the corrected sampled row/column energy log-moment estimate used in the Section 6.1 fixed-matrix sampling proof.
--
--   Under the explicit window assumptions
--   $$
--   1\le \beta\log n,\qquad m\ge 2\beta n\log n,\qquad p={m\over n_1n_2},
--   $$
--   the theorem chooses an integer $q$ with
--   $$
--   q\ge \beta\log n,\qquad q\le 2\beta\log n,\qquad q\le pn,
--   $$
--   and proves
--   $$
--   \mathbb E\max\{R_\Omega(X),C_\Omega(X)\}^q
--   \le
--   \left(Cpn\|X\|_\infty^2\right)^q.
--   $$
--   The reduction combines the repaired integer moment-window lemma, the row-energy half of Lemma 6.2, the column-energy half of Lemma 6.2, and a sample-ratio-safe max-moment combiner.
--
--   Source: Candes-Recht 2008, PDF p. 25, Lemma 6.2, estimate (6.6), and the paragraph immediately following it.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem bernoulli_sampled_row_column_energy_controlled_log_moment_bound_of_two_sample_lower :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (1 : ℝ) ≤ β * Real.log (↑(max n₁ n₂)) →
        (m : ℝ) ≥ 2 * β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
          (q : ℝ) ≤
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X)) ^ q) ≤
            (C * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
  sorry

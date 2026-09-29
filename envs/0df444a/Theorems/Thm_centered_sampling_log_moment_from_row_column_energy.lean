-- Prove2me | Theorems.Thm_centered_sampling_log_moment_from_row_column_energy
-- name    : centered_sampling_log_moment_from_row_column_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:20:24.525062+00:00
-- url     : https://prove2.me/theorems/99f6de23-3449-4146-b483-c764f79fe6bd
-- statement:
--   This is the Section 6.1 log-moment reduction for a fixed matrix under Bernoulli sampling.
--
--   Assume $0<n_1$, $0<n_2$, $m\le n_1n_2$, and choose an integer moment exponent $q$ in the paper's window
--   $$
--   q\gtrsim \beta\log n,\qquad q\le 2\beta\log n,\qquad q\le pn,\qquad p={m\over n_1n_2}.
--   $$
--   If the sampled row/column energy moment is controlled, then Section 6.1 gives
--   $$
--   \mathbb E\left\|p^{-1}(P_\Omega-pI)X\right\|^q
--   \le
--   \left(C\sqrt{\frac{\beta n\log n}{p}}\,\|X\|_\infty\right)^q.
--   $$
--   The reduction uses the repaired sample-ratio symmetrization estimate, the noncommutative-Khintchine row/column energy estimate, and a scalar absorption step converting the $q$ scale to the displayed $\beta\log n$ scale.
--
--   Source: Candes-Recht 2008, PDF pp. 24--25, Section 6.1, equation (6.5), Lemma 6.1, and estimate (6.6).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem centered_sampling_log_moment_from_row_column_energy
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
          (q : ℝ) ≤
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) ∧
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

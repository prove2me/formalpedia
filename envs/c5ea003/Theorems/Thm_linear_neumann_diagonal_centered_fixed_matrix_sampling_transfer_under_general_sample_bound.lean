-- Prove2me | Theorems.Thm_linear_neumann_diagonal_centered_fixed_matrix_sampling_transfer_under_general_sample_bound
-- name    : linear_neumann_diagonal_centered_fixed_matrix_sampling_transfer_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T15:36:45.818015+00:00
-- url     : https://prove2.me/theorems/63d80baf-f3e0-4fb7-9cd5-efa82c128265
-- statement:
--   Deterministic transfer for the centered diagonal part of the first Neumann correction under the full Candès--Recht Theorem 1.3 sample bound.
--
--   Context and notation.  Let $M\in\mathbb R^{n_1\times n_2}$ have rank $r$, SVD data $S$, and let $p=m/(n_1n_2)$ be the Bernoulli sampling rate.  In Section 6.2, the diagonal part $S_0$ of $p^{-1}(P_\Omega-pI)H(E)$ is decomposed in equation (6.9) as a centered sampling fluctuation plus a deterministic mean term.  The centered term has the form
--   $$
--   p^{-1}(1-2p)\sum_{i,j}(\delta_{ij}-p)H_{ij}e_i e_j^\top,
--   $$
--   where
--   $$
--   H_{ij}=p^{-1}E_{ij}\,\langle P_T(e_i e_j^\top),e_i e_j^\top\rangle.
--   $$
--
--   Mathematical claim.  Suppose Theorem 6.3 gives the fixed-matrix centered-sampling bound for $H$, and suppose the rectangular-safe base-entry estimate holds:
--   $$
--   \|H\|_\infty \le C_{\rm base}\,\mu_1\sqrt{\frac r{n_1n_2}}\,{\mu_0 r\over \min(n_1,n_2)}.
--   $$
--   Then, after enlarging the universal constant in the full Theorem 1.3 sample lower bound
--   $$
--   m\ge C'\max\{\mu_1^2,\sqrt{\mu_0}\mu_1,\mu_0 n^{1/4}\}\,nr\,\beta\log n,\qquad n=\max(n_1,n_2),
--   $$
--   the centered diagonal contribution has spectral norm at most $1/32$ with the same high-probability tail as Theorem 6.3.
--
--   Source: Candès--Recht 2008, PDF p. 6, Theorem 1.3/equation (1.9); PDF p. 26, equation (6.9); PDF p. 27, the display after applying Theorem 6.3 to $H$; and the rectangular convention immediately before Section 6.1.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_diagonal_centered_fixed_matrix_sampling_transfer_under_general_sample_bound
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Ccenter ccenter : ℝ, 0 < Ccenter ∧ 0 < ccenter ∧
      ∀ C' : ℝ, Ccenter ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          linearNeumannDiagonalCenteredContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
                (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
              centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannDiagonalBaseMatrix S)) →
        entrySupNorm (linearNeumannDiagonalBaseMatrix S) ≤
          Cbase * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannDiagonalBaseMatrix S)
                (Cfixed * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm (linearNeumannDiagonalBaseMatrix S))) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannDiagonalCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (1 : ℝ) / 32) ≥
          1 - ccenter * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

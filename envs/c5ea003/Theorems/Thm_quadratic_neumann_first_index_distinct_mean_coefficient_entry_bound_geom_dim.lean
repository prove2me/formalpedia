-- Prove2me | Theorems.Thm_quadratic_neumann_first_index_distinct_mean_coefficient_entry_bound_geom_dim
-- name    : quadratic_neumann_first_index_distinct_mean_coefficient_entry_bound_geom_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-04T13:17:52.815639+00:00
-- url     : https://prove2.me/theorems/b3747410-2daa-4628-bb43-daddcb8025c1
-- statement:
--   Honest rectangular form of CR08 Lemma 6.8 (eq. 6.22) for the first-index-distinct mean coefficient matrix $F_{\omega_1}=p^{-1}\sum_{\omega_2\ne\omega_1}E_{\omega_2}P_{\omega_2\omega_2}P_{\omega_2\omega_1}$: under A0 alone, $\|F\|_\infty \le C\,p^{-1}\cdot\frac{\mu_0 r}{\min(n_1,n_2)}\cdot\frac{\mu_0 r}{\sqrt{n_1n_2}}\cdot(1+\frac{\mu_0 r}{\min(n_1,n_2)})$. Route: $pF = P_T(D) - D\circ P_{diag}$ with $D$ the diagonal-kernel-weighted sign matrix; the left/right projection pieces are bounded entrywise by Cauchy-Schwarz against the A0 row/column energies, and the two-sided piece via the spectral bound $\|D\|\le C_{diag}\mu_0 r/\min$ (Lemma 6.4). The min-dimension variant quadratic_neumann_first_index_distinct_mean_coefficient_entry_bound_min_dim carries $(\mu_0r/\min)^2$ with no $\sqrt{n_1n_2}$ and is too weak for the $\lambda^{-3/2}$ threshold in the rectangular regime; this geometric-mean form is what the paper's square-case bound $(\mu_0 r/np)(3\|E\|_\infty + 2\mu_0 r/n)$ actually generalizes to.
-- source:
--   Candes-Recht 2008, Section 6.3 case 2 (Lemma 6.8, eq. 6.22) rectangular form

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_first_index_distinct_mean_coefficient_entry_bound_geom_dim :
    ∃ C68 : ℝ, 0 < C68 ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r) (p : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < p → 1 ≤ μ₀ → A0 S μ₀ →
        entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) ≤
          C68 * p⁻¹ * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
            (μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 + μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by sorry

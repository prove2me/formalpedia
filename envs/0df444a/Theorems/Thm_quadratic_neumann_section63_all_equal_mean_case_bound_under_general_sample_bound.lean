-- Prove2me | Theorems.Thm_quadratic_neumann_section63_all_equal_mean_case_bound_under_general_sample_bound
-- name    : quadratic_neumann_section63_all_equal_mean_case_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T17:17:35.343892+00:00
-- url     : https://prove2.me/theorems/43da1fab-e2da-4598-b5b2-b8c3244c1304
-- statement:
--   This is the deterministic mean part of the all-equal case $\omega_1=\omega_2=\omega_3$ in the Candes-Recht Section 6.3 expansion.
--
--   Source location: Candes-Recht 2008, Section 6.3, PDF pp. 30--31, equation (6.21). After the cubic identity for $\xi_\omega^3$, the non-random term is bounded using Lemma 6.4:
--   $$
--   \left\|\sum_\omega E_\omega P_{\omega\omega}^2F_\omega\right\|\le (2\mu_0r/n)^2.
--   $$
--   This node packages that deterministic estimate at the final Section 6.3 summary scale.
--
--   The scale is the Section 6.3 summary quantity
--   $$
--   \Phi=(\mu_0^2\mu_1)\sqrt{\frac{nr\,\beta\log n}{m}}\left(\frac{nr}{m}\right)^2
--   +\mu_0^2\left(\frac{nr}{m}\right)^2
--   +\sqrt{\beta\log n}\left(\frac{nr}{m}\right)^{3/2}\mu_0^2r
--   +\left(\frac{\mu_0\mu_1nr\,\beta\log n}{m}\right)^{3/2}.
--   $$
--   The theorem states that the deterministic mean contribution has spectral norm at most $C\Phi$ under the full Theorem 1.3 sample lower bound.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_section63_all_equal_mean_case_bound_under_general_sample_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        spectralNorm
            (quadraticNeumannAllEqualMeanContribution S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          (let N : ℝ := ↑(max n₁ n₂)
           let R : ℝ := (r : ℝ)
           let Mobs : ℝ := (m : ℝ)
           let logN : ℝ := Real.log N
           C *
             ((μ₀ ^ 2 * μ₁) *
                Real.sqrt ((N * R * (β * logN)) / Mobs) *
                  ((N * R) / Mobs) ^ 2 +
              μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
              Real.sqrt (β * logN) *
                  Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                    (μ₀ ^ 2 * R) +
              Real.rpow
                ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                ((3 : ℝ) / 2))) := by
  sorry

-- Prove2me | Theorems.Thm_quadratic_neumann_all_equal_mean_factored_scale_from_sample_lower
-- name    : quadratic_neumann_all_equal_mean_factored_scale_from_sample_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T09:06:35.406316+00:00
-- url     : https://prove2.me/theorems/6d5977eb-1f48-4846-90e2-d25021e1d2a3
-- statement:
--   This corrected scalar lemma is the all-equal deterministic-mean sample-size absorption needed in the quadratic Neumann part of the Candes-Recht certificate proof. Write
--   $$p=rac{m}{n_1n_2},qquad n=max(n_1,n_2).$$
--   For every positive base constant $C_{base}$ there is a positive constant $C_{scale}$ such that, under the Lemma 4.6 sample lower bound
--   $$mge lambda,mu_0^{4/3},n,r^{4/3},etalog n,$$
--   with $eta>2$, $lambdage1$, positive dimensions, positive rank, and $mle n_1n_2$, one has
--   $$C_{base},left|p^{-2}(1-3p+2p^2)ight|left(rac{mu_0r}{n}ight)^2le C_{scale},lambda^{-3/2}.$$
--   The retained coefficient $1-3p+2p^2$ is essential: it vanishes at endpoint sampling rates such as $p=1$, which is exactly where the retired unfactored scale lemma failed.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_equal_mean_factored_scale_from_sample_lower
    (Cbase : ℝ) :
    0 < Cbase →
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        Cbase *
            (|((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
                (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                  2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2))| *
              ((μ₀ * (r : ℝ) / (↑(max n₁ n₂))) ^ 2)) ≤
          Cscale * Real.rpow lam (-((3 : ℝ) / 2)) := by
  sorry

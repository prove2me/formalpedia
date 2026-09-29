-- Prove2me | Theorems.Thm_rudelson_min_dim_coordinate_radius_raw_scale_le_one_under_sample_constant
-- name    : rudelson_min_dim_coordinate_radius_raw_scale_le_one_under_sample_constant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T03:13:14.22701+00:00
-- url     : https://prove2.me/theorems/60485e2e-0cdc-4dd2-9b78-5239ac0f07ab
-- statement:
--   This scalar lemma verifies the smallness proviso required before applying the corrected Rudelson selection theorem in Candes-Recht Theorem 4.2.
--
--   The coordinate estimate from equation (4.8) gives the rectangular radius
--   $$
--   R=\sqrt{\frac{C_{\rm coord}\mu_0 r}{\min(n_1,n_2)}}.
--   $$
--   Since the Bernoulli parameter is $p=m/(n_1n_2)$ and $n=\max(n_1,n_2)$, the raw Rudelson scale is
--   $$
--   \sqrt{\frac{\log n}{p}}\,R
--   =
--   \sqrt{\frac{\log n}{m/(n_1n_2)}}\,
--   \sqrt{\frac{C_{\rm coord}\mu_0 r}{\min(n_1,n_2)}}.
--   $$
--   This theorem says that, after increasing the universal sample constant in
--   $$
--   m\ge C'\mu_0 n r\,\beta\log n,
--   $$
--   that raw scale is at most $1$.  This is exactly the missing proviso in equation (4.9), not an extra probabilistic claim.
--
--   Source location: Candes-Recht 2008, PDF pp. 18--19, equations (4.8)--(4.9), especially the phrase after (4.9) requiring the right-hand side to be smaller than $1$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem rudelson_min_dim_coordinate_radius_raw_scale_le_one_under_sample_constant
    (Ccoord : ℝ) :
    0 < Ccoord →
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        Real.sqrt
            (Real.log (↑(max n₁ n₂)) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            Real.sqrt
              (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ≤ 1 := by
  sorry

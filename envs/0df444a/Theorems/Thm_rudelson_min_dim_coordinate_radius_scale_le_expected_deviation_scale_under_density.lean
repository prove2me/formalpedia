-- Prove2me | Theorems.Thm_rudelson_min_dim_coordinate_radius_scale_le_expected_deviation_scale_under_density
-- name    : rudelson_min_dim_coordinate_radius_scale_le_expected_deviation_scale_under_density
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T04:03:34.225439+00:00
-- url     : https://prove2.me/theorems/402346cc-dd15-4f6d-8606-534c2fe41cad
-- statement:
--   Source: Candes-Recht 2008, PDF pp. 18-20, equations (4.8)--(4.10), together with the rectangular convention after (6.4).
--
--   This scalar lemma is the rectangular scale absorption for the corrected Rudelson branch.  Starting from the min-dimension coordinate radius
--   $$
--   R=\sqrt{C_{\mathrm{coord}}\mu_0 r/\min(n_1,n_2)},
--   $$
--   the Rudelson selection scale is
--   $$
--   C_{\mathrm{sel}}\sqrt{\frac{\log n}{p}}R.
--   $$
--   Under $m\le n_1n_2$ and the dense lower bound $m\ge\beta\mu_0nr\log n$, this is absorbed into the theorem scale $C\sqrt{\mu_0nr\log n/m}$ with $n=\max(n_1,n_2)$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem rudelson_min_dim_coordinate_radius_scale_le_expected_deviation_scale_under_density
    (Csel Ccoord : ℝ) :
    0 < Csel → 0 < Ccoord →
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        Csel *
            Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            Real.sqrt
              (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ≤
          tangentSamplingExpectedDeviationScale C μ₀ (max n₁ n₂) r m := by
  sorry

-- Prove2me | Theorems.Thm_quadratic_neumann_first_index_distinct_mean_coefficient_entry_bound_min_dim
-- name    : quadratic_neumann_first_index_distinct_mean_coefficient_entry_bound_min_dim
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T10:21:57.629892+00:00
-- url     : https://prove2.me/theorems/f64454ff-44a3-4319-9dca-0a0841e197dd
-- statement:
--   Corrected (rectangular `min`-denominator) Lemma 6.8 entry bound for the mean
--   coefficient matrix `H` of the `ω₁ ≠ ω₂ = ω₃` quadratic term.
--
--   This is the SOUND replacement for the disproved `r/max` node
--   `quadratic_neumann_first_index_distinct_mean_coefficient_entry_bound` (d5efa6ed):
--   the disproved node used a `μ₁`-free `μ₀² (r/max)²` scale, whereas the honest
--   Candès–Recht Lemma 6.8 (eq. (6.22)) two-term bound is governed by
--   `min(n₁,n₂)` (the §6 rectangular convention) and keeps the `μ₁` sign-envelope:
--
--     `‖H‖∞ ≤ C68 · p⁻¹ · (μ₀ r/min) · (μ₁ √(r/(n₁n₂)) + μ₀ r/min)`.
--
--   The `0 < p` hypothesis is included (unlike the earlier `...lemma68_bound_min_dim`
--   stub, which omitted it and is thereby false for `p < 0`, since `H = p⁻¹ • G` has
--   `entrySup = |p⁻¹|·entrySup G ≥ 0` while the RHS is negative for `p < 0`).
--
--   Source: Candès–Recht 2008, §6.3, Lemma 6.8 (p. 31), eq. (6.22).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_first_index_distinct_mean_coefficient_entry_bound_min_dim :
    ∃ C68 : ℝ, 0 < C68 ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r) (p : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < p →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) ≤
          C68 * p⁻¹ *
            (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
              (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by sorry

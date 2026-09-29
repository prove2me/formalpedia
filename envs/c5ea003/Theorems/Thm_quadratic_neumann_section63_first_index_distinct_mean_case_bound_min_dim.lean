-- Prove2me | Theorems.Thm_quadratic_neumann_section63_first_index_distinct_mean_case_bound_min_dim
-- name    : quadratic_neumann_section63_first_index_distinct_mean_case_bound_min_dim
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T10:29:55.20344+00:00
-- url     : https://prove2.me/theorems/f9cc3fdd-367f-4056-9496-fdb4aaffc638
-- statement:
--   Source: Candès–Recht 2008, Section 6.3, PDF pp. 31--32, the mean part of the
--   `ω₁ ≠ ω₂ = ω₃` case, controlled by Theorem 6.3 applied to the deterministic
--   Lemma-6.8 coefficient matrix `H` **in the honest rectangular `min(n₁,n₂)` scale**.
--
--   This is the SOUND rectangular replacement for the (false-as-stated) node
--   `quadratic_neumann_section63_first_index_distinct_mean_case_bound_under_general_sample_bound`
--   (`e6a57416`).  The original node states the bound at the four-term §6.3 summary
--   scale `Φ` written entirely with `N = max(n₁,n₂)`.  The honest Lemma 6.8 (eq. 6.22)
--   cross-term `2(μ₀ r/min)²` sends its Theorem-6.3 spectral contribution to
--   `√(βlogN)·μ₀²·(N r/m)^{3/2}·√(N r/min)`, which for thin matrices (`min ≪ N`)
--   exceeds every term of the `N`-only `Φ` by an unbounded `(N/min)`-factor.  The
--   minimal sound rectangular correction is to add exactly that `(N/min)`-aware
--   fifth term `t₅ = √(βlogN)·μ₀²·((N R)/M)^{3/2}·√((N R)/min)` to `Φ`.  Then
--
--     * the sign-envelope contribution `Ba` absorbs into the fourth term `t₄`
--       (`Ba/t₄ = 1/(βlogN·√μ₀·√μ₁) ≤ 1`), and
--     * the cross-term contribution `Bb` absorbs into `t₅` (`Bb/t₅ = 1`),
--
--   so the honest Lemma-6.8 bound closes the mean case at scale `Φ + t₅`.  When
--   `n₁ = n₂` (square) `t₅` collapses to `√(βlogN)·μ₀²·(N R/M)^{3/2}·√R` which is `√R`
--   times the third term of `Φ`, so the correction is a genuine rectangular refinement
--   that vanishes (up to constants) in the square case treated by the paper.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_section63_first_index_distinct_mean_case_bound_min_dim :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
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
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannFirstIndexDistinctMeanContribution Omega S
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
                      ((3 : ℝ) / 2) +
                    Real.sqrt (β * logN) * μ₀ ^ 2 *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          Real.sqrt ((N * R) / (↑(min n₁ n₂)))))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry

-- Prove2me | Theorems.Thm_quadratic_neumann_last_index_distinct_response_operator_bound_min_dim
-- name    : quadratic_neumann_last_index_distinct_response_operator_bound_min_dim
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T10:19:42.70966+00:00
-- url     : https://prove2.me/theorems/93fae1e9-77c1-4957-8a8b-93bde11d2297
-- statement:
--   Corrected (rectangular `min`-denominator) Lemma 6.4-style bound for the
--   off-diagonal response operator appearing in the `ω₁ = ω₂ ≠ ω₃` mean term.
--
--   This is the SOUND replacement for the disproved `r/max` node
--   `quadratic_neumann_last_index_distinct_response_operator_bound` (3cd3acbe):
--   the tangent kernel is governed by `min(n₁,n₂)` (CR2009 eqs (4.7)–(4.8), and the
--   rectangular convention "replace n with min(n₁,n₂)" of §6, p. 26), so the
--   diagonal tangent multiplier contributes the `μ₀ r / min` scale.  The remaining
--   tangent projection is measured by the spectral norm of the input matrix.
--
--   Source: Candès–Recht 2008, §6.3, Lemma 6.4 (p. 30), eq. `‖Z‖ ≤ (2 μ₀ r/n)‖X‖`
--   with `n = min(n₁,n₂)`.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_last_index_distinct_response_operator_bound_min_dim :
    ∃ Cresp : ℝ, 0 < Cresp ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → A0 S μ₀ →
        ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (quadraticLastIndexDistinctOffDiagonalResponse S X) ≤
            Cresp * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) * spectralNorm X := by sorry

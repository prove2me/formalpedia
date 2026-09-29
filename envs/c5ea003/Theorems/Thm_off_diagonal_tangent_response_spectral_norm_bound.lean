-- Prove2me | Theorems.Thm_off_diagonal_tangent_response_spectral_norm_bound
-- name    : off_diagonal_tangent_response_spectral_norm_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T01:34:28.334686+00:00
-- url     : https://prove2.me/theorems/d8d51663-f578-42a9-8fde-49481648b03c
-- statement:
--   This theorem gives the deterministic spectral-norm bound for the off-diagonal tangent response operator used in the decoupled first-order and repeated-index quadratic estimates.
--
--   For the operator
--   $$
--   (R_{\mathrm{off}}X)_{ab}=
--   \sum_{(a',b')\ne(a,b)} X_{a'b'}\,
--   \langle P_T(e_{a'}e_{b'}^*),e_ae_b^*\rangle,
--   $$
--   there is a universal constant $C_{\mathrm{resp}}>0$ such that
--   $$
--   \|R_{\mathrm{off}}(X)\|\le C_{\mathrm{resp}}\|X\|.
--   $$
--   The proof writes $R_{\mathrm{off}}X=P_TX-D_TX$, where $D_T$ is the diagonal tangent-kernel multiplier, then combines the universal spectral-norm bounds for $P_T$ and $D_T$.
--
--   Source: Candes-Recht 2008, PDF p. 26, Section 6.2, equations (6.13)--(6.14), using the tangent-kernel formula (6.1) and Lemma 6.4 on PDF p. 27.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem off_diagonal_tangent_response_spectral_norm_bound :
    ∃ Cresp : ℝ, 0 < Cresp ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → A0 S μ₀ →
        ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (offDiagonalTangentResponse S X) ≤
            Cresp * spectralNorm X := by
  sorry

-- Prove2me | Theorems.Thm_tangent_diagonal_multiplier_spectral_norm_bound_from_singular_coordinate_energies
-- name    : tangent_diagonal_multiplier_spectral_norm_bound_from_singular_coordinate_energies
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T17:29:23.945672+00:00
-- url     : https://prove2.me/theorems/079d9870-9f3b-47bf-be20-685ec91991b3
-- statement:
--   This is the core operator-norm estimate in Candes-Recht Lemma 6.4 after the coordinate-energy inputs have been isolated.
--
--   For a fixed matrix $X$, define the diagonal tangent-kernel multiplier
--   $$
--   D_T(X)_{ij}=X_{ij}\,\langle P_T(e_i e_j^\top),e_i e_j^\top\rangle.
--   $$
--   Assume the left and right singular-vector coordinate energies satisfy the A0 scales
--   $$
--   \sum_{k=1}^r u_k(i)^2\le {\mu_0 r\over n_1},\qquad
--   \sum_{k=1}^r v_k(j)^2\le {\mu_0 r\over n_2},
--   $$
--   and also the Bessel bounds by $1$. Then there is a universal constant $C$ such that
--   $$
--   \|D_T(X)\|\le C {\mu_0 r\over \min(n_1,n_2)}\|X\|.
--   $$
--
--   Source: Candes-Recht 2008, PDF p. 27, Lemma 6.4, equations (6.10)--(6.11); PDF p. 24 states that the rectangular case replaces $n$ by $\min(n_1,n_2)$ in the estimates.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem tangent_diagonal_multiplier_spectral_norm_bound_from_singular_coordinate_energies :
    ∃ Cdiag : ℝ, 0 < Cdiag ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ →
        (∀ i : Fin n₁,
          ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₀ * (r : ℝ) / (n₁ : ℝ)) →
        (∀ j : Fin n₂,
          ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₀ * (r : ℝ) / (n₂ : ℝ)) →
        (∀ i : Fin n₁, ∑ k : Fin r, (S.u k i) ^ 2 ≤ (1 : ℝ)) →
        (∀ j : Fin n₂, ∑ k : Fin r, (S.v k j) ^ 2 ≤ (1 : ℝ)) →
        spectralNorm (tangentDiagonalMultiplier S X) ≤
          Cdiag * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
            spectralNorm X := by
  sorry

-- Prove2me | Theorems.Thm_sign_matrix_coordinate_energy_bounds_from_a1
-- name    : sign_matrix_coordinate_energy_bounds_from_a1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T15:57:26.36038+00:00
-- url     : https://prove2.me/theorems/73a3a427-d8d6-421f-8ea3-6ebe0d573c4d
-- statement:
--   This lemma extracts coordinate-energy bounds from the A1 sign-matrix incoherence assumption.
--
--   Let $M$ have rank-$r$ SVD data $S=(u_k,v_k,\sigma_k)$ and let
--   $$
--   E=\sum_{k=1}^r u_k v_k^\top
--   $$
--   be the sign matrix.  The A1 assumption says
--   $$
--   |E_{ij}|\le \mu_1\sqrt{\frac{r}{n_1n_2}}
--   $$
--   for every coordinate $(i,j)$.  Since the rows of $V$ and the rows of $U$ are orthonormal, the row and column Euclidean norms of $E=UV^\top$ are exactly the coordinate energies
--   $$
--   \sum_j E_{ij}^2=\sum_{k=1}^r u_k(i)^2,\qquad
--   \sum_i E_{ij}^2=\sum_{k=1}^r v_k(j)^2.
--   $$
--   Therefore A1 implies
--   $$
--   \sum_{k=1}^r u_k(i)^2\le {\mu_1^2 r\over n_1},\qquad
--   \sum_{k=1}^r v_k(j)^2\le {\mu_1^2 r\over n_2}.
--   $$
--
--   Source: Candes-Recht 2008, PDF p. 4, assumption A1, together with the SVD orthonormality identities used throughout Section 6.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem sign_matrix_coordinate_energy_bounds_from_a1 :
    ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₁ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₁ → A1 S μ₁ →
      (∀ i : Fin n₁,
        ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₁ ^ 2 * (r : ℝ) / (n₁ : ℝ)) ∧
      (∀ j : Fin n₂,
        ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₁ ^ 2 * (r : ℝ) / (n₂ : ℝ)) := by
  sorry

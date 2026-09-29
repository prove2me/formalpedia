-- Prove2me | Theorems.Thm_sampled_rank_one_rademacher_average_bound_from_radius_and_gram_opnorm
-- name    : sampled_rank_one_rademacher_average_bound_from_radius_and_gram_opnorm
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-26T00:09:01.362911+00:00
-- url     : https://prove2.me/theorems/86d7a511-f716-44e3-b77a-6f8dd2a52207
-- statement:
--   This is a formal bridge below `inner_sign_average_khintchine_variance_proxy_bound_of_two_le_max` (`f4806ebd`), not a theorem stated verbatim in Candes--Recht.
--
--   Source: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9), where the Rudelson expectation estimate is used for the tangent sampling deviation. The analytic input is Rudelson, *Random vectors in the isotropic position*, JFA 164 (1999), Theorem 1, proof Steps 1--2, together with the Lust-Picquard/Pisier noncommutative Khintchine inequality.
--
--   Mathematical statement. Let `alpha` be a finite coordinate type with `d = |alpha|`, let `N` be the ambient dimension scale with `2 <= N` and `d <= N^2`, and let `Omega : Finset alpha` be a fixed sampled coordinate set. For each coordinate `c`, let
--   $$
--   y_c \in \mathbb R^{\alpha},\qquad \|y_c\|_2^2 \le R^2,
--   $$
--   with `0 <= R`. Define the sampled Gram operator
--   $$
--   G_\Omega=\sum_{c\in\Omega} y_c y_c^\top.
--   $$
--   Then there is a universal constant `Csym0 > 0` such that
--   $$
--   \mathbb E_\varepsilon\left\|\sum_c \varepsilon_c\mathbf 1_{c\in\Omega} y_c y_c^\top\right\|
--   \le
--   C_{\rm sym}\sqrt{\log N}\,R\,\sqrt{\|G_\Omega\|}.
--   $$
--   In the downstream Candes--Recht tangent-space use, `alpha = Fin n1 × Fin n2`, `N = n = max(n1,n2)`, `p = m/(n1 n2)` is the Bernoulli sampling rate, `Omega` is one fixed Bernoulli sample realization, and `y_ab` is the vectorized projected coordinate matrix `P_T(e_a e_b^*)`. The incoherence parameters `mu_0` and `mu_1` do not appear in this bridge; they enter upstream only to prove the radius bound on `y_ab`.
--
--   Formalization note: this is a formal bridge. It imports the source-backed child `reindexed_rademacher_matrix_operator_norm_first_moment_log_window_from_2p`, whose source is Candes--Recht PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9), and the source-backed child `rank_one_variance_proxy_eigenvalue_le_radius_sq_gram_opnorm`, whose source is the same Rudelson/Candes--Recht variance-proxy step. It only performs finite-coordinate reindexing, sampled-indicator algebra, Hermitian checks for rank-one matrices, and the scalar identity `sqrt(R^2 * ||G_Omega||) = R * sqrt(||G_Omega||)`.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. Exact Matrix Completion via Convex Optimization. arXiv:0805.4471 / Foundations of Computational Mathematics 9 (2009), 717--772. Exact location: PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9). Rudelson, Mark. Random vectors in the isotropic position. JFA 164 (1999), Theorem 1, proof Steps 1--2, with the Lust-Picquard/Pisier noncommutative Khintchine inequality.

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.EquivFin

open Matrix MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

theorem sampled_rank_one_rademacher_average_bound_from_radius_and_gram_opnorm :
    ∃ Csym0 : ℝ, 0 < Csym0 ∧
      ∀ {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ},
        0 < Fintype.card α → 2 ≤ N → Fintype.card α ≤ N * N →
        ∀ (y : α → α → ℝ) (R : ℝ),
        0 ≤ R →
        (∀ c : α, (y c ⬝ᵥ y c) ≤ R ^ 2) →
        ∀ (Omega : Finset α),
        (∑ eps : Finset α, ((1:ℝ)/2) ^ (Fintype.card α) *
          ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
            (∑ c : α, (((if c ∈ eps then (1:ℝ) else -1) *
                (if c ∈ Omega then (1:ℝ) else 0)) •
              Matrix.vecMulVec (y c) (y c)))))‖)
        ≤ Csym0 *
            (Real.sqrt (Real.log (N : ℝ)) * R) *
            Real.sqrt
              ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                (∑ c : α, (if c ∈ Omega then (1:ℝ) else 0) •
                  Matrix.vecMulVec (y c) (y c))))‖ := by
  sorry

-- Prove2me | Theorems.Thm_rank_one_variance_proxy_eigenvalue_le_radius_sq_gram_opnorm
-- name    : rank_one_variance_proxy_eigenvalue_le_radius_sq_gram_opnorm
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-25T22:16:43.536621+00:00
-- url     : https://prove2.me/theorems/ad71e79c-1af4-49aa-b49c-58c55c4be05c
-- statement:
--   This is a formal bridge for the variance-proxy assembly in the Rudelson/Lust-Picquard noncommutative-Khintchine step used by the Candes--Recht tangent-sampling route.
--
--   Source: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9), together with Rudelson, *Random vectors in the isotropic position*, JFA 164 (1999), Theorem 1, proof Steps 1--2, and the Lust-Picquard/Pisier noncommutative Khintchine inequality.
--
--   Mathematical statement. Let $y_c \in \mathbb R^d$ be a finite family of vectors indexed by $c \in s$. Define the sampled Gram operator and the variance operator by
--   $$
--   G=\sum_{c\in s} y_c\otimes y_c,\qquad
--   V=\sum_{c\in s}(y_c\otimes y_c)^2.
--   $$
--   If $0\le R$ and $\|y_c\|^2\le R^2$ for every $c\in s$, then every eigenvalue of the Hermitian variance matrix $V$ is bounded by
--   $$
--   \lambda_i(V)\le R^2\,\|G\|_{\ell^2\to\ell^2}.
--   $$
--
--   Variables and notation. In the downstream Exact Matrix Completion route, $n=\max(n_1,n_2)$, $p=m/(n_1n_2)$ is the Bernoulli sampling rate, and $\Omega$ is a fixed Bernoulli sample realization. The family $y_c$ will be $y_{ab}=P_T(e_a e_b^\top)$ restricted to sampled coordinates $ab\in\Omega$, with the coordinate radius bound supplied by $\|y_{ab}\|_F\le R$. The incoherence parameters $\mu_0$ and $\mu_1$ enter upstream only to prove that radius bound; they are not hypotheses of this purely finite-dimensional operator bridge.
--
--   Formalization note. This is a formal bridge, not a theorem appearing verbatim in Candes--Recht. It bridges the proved source-backed imports `sum_rank_one_outer_product_square_collapse` (`f76d68af`) and `rudelson_selection_gram_spectral_bound` (`8958d37d`) to the source-backed child route through `rademacher_matrix_operator_norm_first_moment_log_window_from_2p` (`136263d8`) and `inner_sign_average_khintchine_variance_proxy_bound_of_two_le_max` (`f4806ebd`). The proof should use $(y\otimes y)^2=\|y\|^2(y\otimes y)$, the proved one-sided Gram spectral bound, and the standard Hermitian fact that an eigenvalue is bounded by the $\ell^2$ operator norm.
-- source:
--   Candes--Recht, Exact Matrix Completion via Convex Optimization, PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9); Rudelson, Random vectors in the isotropic position, JFA 164 (1999), Theorem 1, proof Steps 1--2; Lust-Picquard/Pisier noncommutative Khintchine; existing source-backed platform imports `sum_rank_one_outer_product_square_collapse` (`f76d68af`) and `rudelson_selection_gram_spectral_bound` (`8958d37d`).

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open Matrix
open scoped BigOperators Matrix Matrix.Norms.L2Operator MatrixOrder

theorem rank_one_variance_proxy_eigenvalue_le_radius_sq_gram_opnorm
    {d : Nat} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (y : ι → Fin d → ℝ) (R : ℝ)
    (hR_nonneg : 0 ≤ R)
    (hRadius : ∀ c ∈ s, (y c ⬝ᵥ y c) ≤ R ^ 2) :
    let G : Matrix (Fin d) (Fin d) ℝ :=
      ∑ c ∈ s, Matrix.vecMulVec (y c) (y c)
    let V : Matrix (Fin d) (Fin d) ℝ :=
      ∑ c ∈ s, Matrix.vecMulVec (y c) (y c) * Matrix.vecMulVec (y c) (y c)
    (hGHerm : G.IsHermitian) →
    (hVHerm : V.IsHermitian) →
    ∀ i : Fin d,
      hVHerm.eigenvalues i ≤
        R ^ 2 * ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin G))‖ := by
  sorry

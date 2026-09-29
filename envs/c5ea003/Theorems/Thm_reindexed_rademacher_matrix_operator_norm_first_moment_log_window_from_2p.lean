-- Prove2me | Theorems.Thm_reindexed_rademacher_matrix_operator_norm_first_moment_log_window_from_2p
-- name    : reindexed_rademacher_matrix_operator_norm_first_moment_log_window_from_2p
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-25T23:25:28.644858+00:00
-- url     : https://prove2.me/theorems/47dda0b4-974f-4535-9b90-6d9b8169e808
-- statement:
--   This is a formal bridge for the Rudelson/Lust-Picquard noncommutative-Khintchine step in the Candes--Recht tangent-sampling route.
--
--   Source: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9), together with Rudelson, *Random vectors in the isotropic position*, JFA 164 (1999), Theorem 1, proof Steps 1--2, and the Lust-Picquard/Pisier noncommutative Khintchine inequality.
--
--   Mathematical statement. Let $\iota$ be a finite Rademacher sign index set and let $\alpha$ be an arbitrary finite matrix coordinate type. Write $d=|\alpha|$ and choose the canonical equivalence $e:\operatorname{Fin}(d)\simeq\alpha$. For Hermitian matrices $H_c\in\mathbb R^{\alpha\times\alpha}$, define $H'_c=H_c[e,e]\in\mathbb R^{d\times d}$ by reindexing rows and columns along $e$. If
--   $$
--   V'=\sum_{c\in\iota}(H'_c)^2,\qquad \lambda_i(V')\le\nu\quad\text{for all }i,
--   $$
--   with $\nu\ge0$, $0<d$, $2\le N$, and $d\le N^2$, then the already source-backed log-window inequality gives
--   $$
--   \mathbb E_\varepsilon\left\|\sum_{c\in\iota}\varepsilon_cH_c\right\|
--   \le C_{\log}\sqrt{\log N}\sqrt{\nu}.
--   $$
--   This bridge records that the operator norm is invariant under the finite reindexing $e$.
--
--   Variables and notation. In the downstream Exact Matrix Completion mission, $N=n=\max(n_1,n_2)$, $p=m/(n_1n_2)$ is the Bernoulli sampling rate, $\Omega$ is the fixed Bernoulli sample realization, and $\alpha=\operatorname{Fin}(n_1)\times\operatorname{Fin}(n_2)$. The matrices $H_c$ are later instantiated as $\mathbf 1_{c\in\Omega}(y_c\otimes y_c)$, where $y_c=P_T(e_ie_j^*)$. The incoherence parameters $\mu_0$ and $\mu_1$ are upstream inputs used to bound the tangent-coordinate radius; they are not hypotheses of this purely formal reindexing node. The probability model in this node is only the auxiliary uniform Rademacher sign average over $\varepsilon_c\in\{-1,1\}$.
--
--   Formalization note. This is a formal bridge, not a theorem appearing verbatim in Candes--Recht. It bridges the source-backed proved child `rademacher_matrix_operator_norm_first_moment_log_window_from_2p` (`136263d8`) and the proved formal reindexing import `opnorm_submatrix_equiv` (`e66e5c47`) to the live source-backed Rudelson child route for `inner_sign_average_khintchine_variance_proxy_bound_of_two_le_max` (`f4806ebd`). It adds no new concentration estimate; it only transports the finite-dimensional matrix index from `Fin d` to an arbitrary finite type.
-- source:
--   Candes--Recht, Exact Matrix Completion via Convex Optimization, PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9); Rudelson, Random vectors in the isotropic position, JFA 164 (1999), Theorem 1, proof Steps 1--2; Lust-Picquard/Pisier noncommutative Khintchine; source-backed platform imports `rademacher_matrix_operator_norm_first_moment_log_window_from_2p` (`136263d8`) and `opnorm_submatrix_equiv` (`e66e5c47`).

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.EquivFin

open Matrix MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

theorem reindexed_rademacher_matrix_operator_norm_first_moment_log_window_from_2p :
    ∃ Clog : ℝ, 0 < Clog ∧
      ∀ {ι α : Type*} [Fintype ι] [DecidableEq ι]
        [Fintype α] [DecidableEq α] {N : ℕ},
        0 < Fintype.card α → 2 ≤ N → Fintype.card α ≤ N * N →
        ∀ (H : ι → Matrix α α ℝ),
        (∀ c, (H c).IsHermitian) →
        ∀ (normV : ℝ), 0 ≤ normV →
        let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
        let Hfin : ι → Matrix (Fin (Fintype.card α)) (Fin (Fintype.card α)) ℝ :=
          fun c => (H c).submatrix e e
        (hVHerm : (∑ c : ι, Hfin c * Hfin c).IsHermitian) →
        (∀ i, hVHerm.eigenvalues i ≤ normV) →
        (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
          ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
            (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c)))‖)
        ≤ Clog * Real.sqrt (Real.log (N : ℝ)) * Real.sqrt normV := by
  sorry

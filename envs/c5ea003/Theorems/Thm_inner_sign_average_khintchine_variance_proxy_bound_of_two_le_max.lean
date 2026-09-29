-- Prove2me | Theorems.Thm_inner_sign_average_khintchine_variance_proxy_bound_of_two_le_max
-- name    : inner_sign_average_khintchine_variance_proxy_bound_of_two_le_max
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-25T14:17:11.360958+00:00
-- url     : https://prove2.me/theorems/f4806ebd-b5d8-4ed1-b5fd-1a4ff5ba5913
-- statement:
--   Corrected (max $\ge 2$) variant of `inner_sign_average_khintchine_variance_proxy_bound` (carve B, Rudelson 1999 JFA 164, Theorem 1 Step 2; matrix non-commutative Khintchine / Lust-Picquard on the rank-one tangent tensors). For every $\beta$-free size with $0<n_1,0<n_2,0<r,m\le n_1 n_2$, $2\le\max(n_1,n_2)$, radius bound $\|P_T(e_ie_j^*)\|_F\le R$, and every fixed sample set $\Omega$: the Rademacher sign-average $\mathbb E_\varepsilon\,\|\sum_{ab}\varepsilon_{ab}\,\delta_{ab}\,(y_{ab}\otimes y_{ab})\|$ (with $y_{ab}=P_T(e_ae_b^*)$) is bounded by $C_{sym0}\,\sqrt{\log(\max n_1 n_2)}\,R\,\sqrt{\|G_\Omega\|}$, where $G_\Omega=\sum_{ab\in\Omega}y_{ab}\otimes y_{ab}$ is the unsigned sampled Gram operator. The hypothesis $2\le\max(n_1,n_2)$ makes $\log(\max n_1 n_2)>0$ and removes the $\sqrt{\log 1}=0$ edge defect of the original node (which was false at $n_1=n_2=1$, RHS $=0$ but LHS $>0$). This is the genuine Mathlib-absent operator-space content of the Rudelson selection route; the $\max=1$ case is handled separately in the parent (the centered fluctuation collapses to $0$ when $p\in\{0,1\}$).
-- source:
--   Rudelson 1999, J. Funct. Anal. 164, 60-72, Theorem 1 (Steps 1-2); Candes-Recht 2009, arXiv:0805.4471, Section 4.2, Theorem 4.2 eq (4.9); Lust-Picquard 1986 / Pisier (noncommutative Khintchine).

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

theorem inner_sign_average_khintchine_variance_proxy_bound_of_two_le_max :
    ∃ Csym0 : ℝ, 0 < Csym0 ∧
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (R : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        2 ≤ max n₁ n₂ →
        0 ≤ R →
        (∀ i : Fin n₁, ∀ j : Fin n₂,
          frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R) →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂)),
        (∑ Es : Finset (Fin n₁ × Fin n₂),
            ((1:ℝ)/2) ^ (Fintype.card (Fin n₁ × Fin n₂)) *
              ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                (∑ ab : Fin n₁ × Fin n₂,
                  (((if ab ∈ Es then (1:ℝ) else -1) *
                      (if ab ∈ Omega then (1:ℝ) else 0)) •
                    Matrix.vecMulVec
                      (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                      (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖)
          ≤ Csym0 *
              (Real.sqrt (Real.log (↑(max n₁ n₂))) * R) *
              Real.sqrt
                ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                  (∑ ab : Fin n₁ × Fin n₂,
                    (if ab ∈ Omega then (1:ℝ) else 0) •
                      Matrix.vecMulVec
                        (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                        (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))))‖ := by
  sorry

-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_kernel_square_base_frobenius_norm_bound_min_dim
-- name    : quadratic_neumann_middle_index_distinct_kernel_square_base_frobenius_norm_bound_min_dim
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-23T05:49:33.181981+00:00
-- url     : https://prove2.me/theorems/030700a5-71f3-4a5d-a146-db278d3a434e
-- statement:
--   **Frobenius bound for the off-diagonal kernel-square base matrix** (Candes–Recht 2009, §6 eq (6.2) with the Bessel identity (4.7), p.32). For the same $\omega_1=\omega_3\ne\omega_2$ base matrix with entries $K(w_1,(i,j))K((i,j),w_1)$, the Frobenius norm is bounded by $$\|\,\cdot\,\|_F\ \le\ C_{\mathrm{fro}}\,\mu_0^{3/2}\,\Big(\frac{r}{\min(n_1,n_2)}\Big)^{3/2}.$$ Proof: $\|\,\cdot\,\|_F^2\le C_{\mathrm{ker}}^2\sum_{ij}K(w_1,(i,j))^2 = C_{\mathrm{ker}}^2\,\|P_T e_{w_1}\|_F^2 = C_{\mathrm{ker}}^2\,K(w_1,w_1)\le C_{\mathrm{ker}}^3(\mu_0 r/\min)^3$, using the off-diagonal bound on the $K((i,j),w_1)$ factor and the diagonal identity (4.7) on the sum of $K(w_1,\cdot)^2$. Taking square roots gives $C_{\mathrm{fro}}=C_{\mathrm{ker}}^{3/2}$. This corrects the disproved $\max$ supplier.
-- source:
--   Candes & Recht, Exact Matrix Completion via Convex Optimization (2009), arXiv:0805.4471, §6 "Proofs of the Critical Lemmas", p.32, eq (6.1)+(6.2).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_kernel_square_base_frobenius_norm_bound_min_dim :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
            Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
              Real.rpow ((r : ℝ) / (↑(min n₁ n₂))) ((3 : ℝ) / 2) := by sorry

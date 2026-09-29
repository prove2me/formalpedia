-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_kernel_square_base_entry_sup_norm_bound_min_dim
-- name    : quadratic_neumann_middle_index_distinct_kernel_square_base_entry_sup_norm_bound_min_dim
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-23T05:49:12.335808+00:00
-- url     : https://prove2.me/theorems/ca93a571-41e2-4b8e-922f-da7b7869f827
-- statement:
--   **Entry-sup bound for the off-diagonal kernel-square base matrix** (Candes–Recht 2009, §6 eq (6.2), p.32). For the base matrix of the $\omega_1=\omega_3\ne\omega_2$ middle-index-distinct quadratic Neumann term, whose $(i,j)$ entry is the product of two off-diagonal kernels $K(w_1,(i,j))\cdot K((i,j),w_1)$ (and $0$ when $(i,j)=w_1$), the entrywise sup-norm is bounded by $$\|\,\cdot\,\|_{\infty}\ \le\ C_{\mathrm{entry}}\,\mu_0^2\,\Big(\frac{r}{\min(n_1,n_2)}\Big)^2.$$ Each kernel factor satisfies $|K|\le C_{\mathrm{ker}}\mu_0\,r/\min(n_1,n_2)$ by the off-diagonal magnitude bound, so each entry is $\le (C_{\mathrm{ker}}\mu_0 r/\min)^2$; thus $C_{\mathrm{entry}}=C_{\mathrm{ker}}^2$. This is the dimension-correct $\min$ form correcting the disproved $\max$ supplier (which had $(r/\max)^2$).
-- source:
--   Candes & Recht, Exact Matrix Completion via Convex Optimization (2009), arXiv:0805.4471, §6 "Proofs of the Critical Lemmas", p.32, eq (6.1)+(6.2).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_kernel_square_base_entry_sup_norm_bound_min_dim :
    ∃ Centry : ℝ, 0 < Centry ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
            Centry * μ₀ ^ 2 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 2) := by sorry

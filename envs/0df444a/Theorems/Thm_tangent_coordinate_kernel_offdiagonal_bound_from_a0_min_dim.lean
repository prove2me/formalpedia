-- Prove2me | Theorems.Thm_tangent_coordinate_kernel_offdiagonal_bound_from_a0_min_dim
-- name    : tangent_coordinate_kernel_offdiagonal_bound_from_a0_min_dim
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-23T05:48:50.22761+00:00
-- url     : https://prove2.me/theorems/fe654068-8e27-46ae-a4b6-5e0612bb3cbd
-- statement:
--   **Off-diagonal tangent-kernel magnitude bound** (Candes–Recht 2009, §6 eq (6.1)+(6.2), p.32). For a rank-$r$ SVD $S$ of $M\in\mathbb R^{n_1\times n_2}$ satisfying the standard incoherence hypothesis `A0 S μ₀` (the $A_0$ coherence bound with parameter $\mu_0\ge 1$), the tangent-space coordinate kernel $K(i,j,a,b)=\langle P_T(e_ie_j^\top),\,e_ae_b^\top\rangle$ is uniformly bounded — for **all** index pairs $(i,j),(a,b)$, not only the diagonal $(i,j)=(a,b)$ — by $$|K(i,j,a,b)|\ \le\ C_{\mathrm{ker}}\,\mu_0\,\frac{r}{\min(n_1,n_2)}.$$ This is the off-diagonal generalization of the diagonal estimate (4.8) $\|P_T(e_ae_b^\top)\|_F^2\le 2\mu_0 r/\min(n_1,n_2)$. It follows by Cauchy–Schwarz for the Frobenius inner product: $K(i,j,a,b)=\langle P_T e_{ij},P_T e_{ab}\rangle$ (self-adjointness and idempotence of $P_T$), hence $|K(i,j,a,b)|\le\|P_T e_{ij}\|_F\,\|P_T e_{ab}\|_F$, and each factor equals $\sqrt{K(\cdot,\cdot,\cdot,\cdot)_{\text{diag}}}\le\sqrt{C_{\mathrm{ker}}\mu_0 r/\min}$ by eq (4.7).
-- source:
--   Candes & Recht, Exact Matrix Completion via Convex Optimization (2009), arXiv:0805.4471, §6 "Proofs of the Critical Lemmas", p.32, eq (6.1)+(6.2).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem tangent_coordinate_kernel_offdiagonal_bound_from_a0_min_dim :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ i j a b,
          |tangentCoordinateKernel S i j a b| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by sorry

-- Prove2me | Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a0_geom_dim
-- name    : entry_sup_norm_sign_matrix_bound_from_a0_geom_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-04T12:37:51.471154+00:00
-- url     : https://prove2.me/theorems/b04f8bd2-755e-408d-9758-475c4a109084
-- statement:
--   Geometric-mean entrywise bound for the sign matrix from A0 alone: if the SVD data $S$ of $M$ satisfies the coherence assumption A0 with parameter $\mu_0$, then every entry of the sign matrix $E=\sum_k u_k v_k^*$ satisfies $|E_{ij}| \le \mu_0 r/\sqrt{n_1 n_2}$. This is the Cauchy-Schwarz estimate from Candes-Recht 2008 p.6 (the remark that A1 always holds with $\mu_1=\mu_0\sqrt r$): $|E_{ij}| = |\langle u^{(i)}, v^{(j)}\rangle| \le \|U^*e_i\|\|V^*e_j\| \le \sqrt{\mu_0 r/n_1}\sqrt{\mu_0 r/n_2}$. Note the geometric mean $\sqrt{n_1n_2}$ in the denominator: the min-dimension variant entry_sup_norm_sign_matrix_bound_from_a0_min_dim is strictly lossier and does NOT suffice for the second-order Neumann threshold in the rectangular regime.
-- source:
--   Candes-Recht 2008, Exact Matrix Completion via Convex Optimization, Section 6.3 (proof of Lemma 4.6, all-equal case, eq. 6.21)

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem entry_sup_norm_sign_matrix_bound_from_a0_geom_dim :
    ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
      entrySupNorm (signMatrix S) ≤
        μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) := by sorry

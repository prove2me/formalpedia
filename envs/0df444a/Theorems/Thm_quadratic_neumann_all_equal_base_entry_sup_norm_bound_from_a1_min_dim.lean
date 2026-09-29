-- Prove2me | Theorems.Thm_quadratic_neumann_all_equal_base_entry_sup_norm_bound_from_a1_min_dim
-- name    : quadratic_neumann_all_equal_base_entry_sup_norm_bound_from_a1_min_dim
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-30T18:34:21.494238+00:00
-- url     : https://prove2.me/theorems/7330ddb8-a2bc-400e-9358-09294daf4759
-- statement:
--   A1-sharp corrected rectangular entry-supremum bound for the all-equal quadratic base matrix in the centered part of Candes--Recht Lemma 4.6.
--
--   Primary reference: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 4, Section 1.2, assumption A1; PDF p. 27, Section 6.2, Lemma 6.4; and PDF pp. 30--31, Section 6.3, equation (6.21).
--
--   Mathematical statement and notation: let $S$ be rank-$r$ SVD data for an $n_1\times n_2$ matrix satisfying the incoherence hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$. Let $d=\min(n_1,n_2)$. In the all-equal case $\omega_1=\omega_2=\omega_3$ of Section 6.3, equation (6.21) uses the fixed matrix
--   $$
--   B^{=}_{\omega}=E_{\omega} P_{\omega\omega}^2 F_{\omega},
--   $$
--   represented in Lean by `quadraticNeumannAllEqualBaseMatrix S`. The A1 assumption gives the sign-matrix entry scale
--   $$
--   |E_{ij}|\le \mu_1\sqrt{\frac{r}{n_1n_2}},
--   $$
--   and Lemma 6.4 gives the corrected rectangular diagonal tangent-kernel scale
--   $$
--   P_{\omega\omega}\lesssim {\mu_0 r\over d}.
--   $$
--   Therefore this node asserts the source-corrected A1-sharp entry bound
--   $$
--   \|B^{=}\|_{\infty}
--   \le C_{\rm base}\,\mu_1\sqrt{\frac{r}{n_1n_2}}
--   \left({\mu_0 r\over \min(n_1,n_2)}\right)^2.
--   $$
--   Here $n=\max(n_1,n_2)$, $d=\min(n_1,n_2)$, $r$, $\mu_0$, $\mu_1$, and the SVD/incoherence hypotheses are explicit. The Bernoulli rate $p=m/(n_1n_2)$, $Z(\Omega)$, and fixed-cardinality `successProb` do not appear in this deterministic base-matrix estimate.
--
--   Formalization note: this is a source-derived mathematical child, not a theorem stated verbatim in the paper and not a purely formal Lean bridge. It complements the already-proved A0-only min-dimension theorem `quadratic_neumann_all_equal_base_entry_sup_norm_bound_min_dim`, whose scale $\mu_0^3(r/\min(n_1,n_2))^3$ is too coarse for the Section 6.3 summary scale when the sharper A1 sign-entry factor is available. A later formal bridge should combine this child with `fixed_matrix_centered_sampling_spectral_bound` and `quadratic_neumann_all_equal_centered_as_fixed_matrix_fluctuation` to prove the Section 6.3 all-equal centered case `quadratic_neumann_section63_all_equal_centered_case_bound_under_general_sample_bound`.
-- source:
--   Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 4, Section 1.2, assumption A1; PDF p. 27, Section 6.2, Lemma 6.4; PDF pp. 30--31, Section 6.3, equation (6.21).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_equal_base_entry_sup_norm_bound_from_a1_min_dim :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2 := by
  sorry

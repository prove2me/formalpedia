-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_structural_a0_min_dim
-- name    : quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_structural_a0_min_dim
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-30T14:06:38.995613+00:00
-- url     : https://prove2.me/theorems/f50ee811-91b0-4f3d-94ad-05c018d65861
-- statement:
--   Structural A0-based pointwise tail for the all-distinct inner coefficient in the quadratic Neumann term.
--
--   Primary reference: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 6, Section 1.2, Definition 1.2 and the paragraph before Theorem 1.3, with Theorem 1.3 equation (1.9), where the paper notes that $A1$ holds with $\mu_1=\mu_0\sqrt r$ by Cauchy--Schwarz; PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17), for the scalar Bernstein coordinate bound; and PDF p. 30, Section 6.3, equation (6.20), for the all-distinct inner coefficient representation.
--
--   Mathematical statement and notation: let $n=\max(n_1,n_2)$ and $p=m/(n_1n_2)$.  The sample set $\Omega_3$ is drawn from the independent Bernoulli model with rate $p$, represented in Lean by `bernoulliEventProb p`.  Let $S$ be rank-$r$ SVD data for an $n_1\times n_2$ matrix satisfying $A0(S,\mu_0)$; the statement also carries the ambient $A1(S,\mu_1)$ hypothesis used by surrounding nodes, but the intended structural route uses the Candes--Recht Cauchy--Schwarz consequence $A1(S,\mu_0\sqrt r)$ instead of the possibly loose input $\mu_1$.
--
--   For coordinates $w_1,w_2\in[n_1]\times[n_2]$, equation (6.20) identifies the all-distinct inner coefficient with a centered scalar sampling fluctuation
--   $$
--   G_{w_1,w_2}(\Omega_3)=\sum_{i,j}(\delta_{ij}-p)B^{\rm all}_{w_1,w_2}(i,j).
--   $$
--   Under the Lemma 6.6 density floor
--   $$
--   m\ge \lambda\mu_0^{4/3}n r^{4/3}\beta\log n,
--   $$
--   the theorem asserts the fixed-coordinate pointwise tail
--   $$
--   \mathbb P_p\{|G_{w_1,w_2}(\Omega_3)|\le C_{\rm point}\lambda^{-1/2}\}
--   \ge 1-c_{\rm point}n^{-\beta}.
--   $$
--   Here $p,n,\Omega_3,\mu_0,\mu_1$, $r$, $\lambda$, and the Bernoulli probability model are explicit.  $Z(\Omega)$ and fixed-cardinality `successProb` do not appear in this local coefficient theorem.
--
--   Formalization note: this is a source-derived structural child, not a theorem stated verbatim in the paper and not a purely formal Lean bridge.  It is meant to replace a direct absorption from the raw two-term theorem using the loose input $\mu_1$.  A proof should combine the source-backed raw scalar Bernstein child `quadratic_neumann_all_distinct_inner_coefficient_pointwise_two_term_tail_from_base_bounds_min_dim`, the Candes--Recht $A0\Rightarrow A1(\mu_0\sqrt r)$ Cauchy--Schwarz step, the corrected all-distinct min-dimension base-bound suppliers, and scalar absorption under the displayed density floor.
-- source:
--   Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 6, Section 1.2, Definition 1.2 and paragraph before Theorem 1.3, with Theorem 1.3 equation (1.9); PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17); PDF p. 30, Section 6.3, equation (6.20).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_structural_a0_min_dim :
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ (Omega3 : Finset (Fin n₁ × Fin n₂))
            (w1 w2 : Fin n₁ × Fin n₂),
          quadraticAllDistinctInnerCoefficient Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega3
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctInnerBaseMatrix S w1 w2))) →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega3 =>
                |quadraticAllDistinctInnerCoefficient Omega3 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2| ≤
                  Cpoint * Real.rpow lam (-((1 : ℝ) / 2))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

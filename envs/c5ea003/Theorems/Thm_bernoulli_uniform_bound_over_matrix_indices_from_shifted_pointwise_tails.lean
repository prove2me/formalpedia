-- Prove2me | Theorems.Thm_bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
-- name    : bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T22:45:25.646823+00:00
-- url     : https://prove2.me/theorems/1b13a4d2-dffe-48b6-98b2-53afd812dd68
-- statement:
--   This is the corrected finite union bound over matrix coordinates.
--
--   Assume $p\in[0,1]$ and let $n=\max(n_1,n_2)$. For each coordinate $w=(i,j)$, suppose
--   $$
--   \mathbb P_p\{|\operatorname{Coeff}_w(\Omega)|\le C_{\rm point}s\}\ge 1-c_{\rm point}n^{-(\beta+2)}.
--   $$
--   Then the simultaneous coordinate event satisfies
--   $$
--   \mathbb P_p\{\forall w,\ |\operatorname{Coeff}_w(\Omega)|\le C_{\rm uniform}s\}
--   \ge 1-c_{\rm uniform}n^{-\beta}.
--   $$
--
--   The two-power shift from $\beta+2$ to $\beta$ is exactly the cost of the coordinate union bound, since $n_1n_2\le n^2$.
--
--   Source context. Candes-Recht 2008, PDF p. 29, applies a union bound after equation (6.17) to upgrade pointwise coefficient estimates to uniform coordinate estimates.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∃ Cuniform cuniform : ℝ, 0 < Cuniform ∧ 0 < cuniform ∧
      ∀ (β p scale : ℝ), 2 < β → 0 ≤ p → p ≤ 1 →
      ∀ (n₁ n₂ : ℕ),
        0 < n₁ → 0 < n₂ →
        ∀ Coeff : (Fin n₁ × Fin n₂) →
          Finset (Fin n₁ × Fin n₂) → ℝ,
        (∀ w : Fin n₁ × Fin n₂,
          bernoulliEventProb p
              (fun Omega => |Coeff w Omega| ≤ Cpoint * scale) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2))) →
        bernoulliEventProb p
            (fun Omega =>
              ∀ w : Fin n₁ × Fin n₂,
                |Coeff w Omega| ≤ Cuniform * scale) ≥
          1 - cuniform * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

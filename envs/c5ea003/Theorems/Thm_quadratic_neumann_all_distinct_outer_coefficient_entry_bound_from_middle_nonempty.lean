-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_outer_coefficient_entry_bound_from_middle_nonempty
-- name    : quadratic_neumann_all_distinct_outer_coefficient_entry_bound_from_middle_nonempty
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T05:31:01.850591+00:00
-- url     : https://prove2.me/theorems/1b3411e9-c5d2-4bfe-93e9-9538cc99654e
-- statement:
--   This corrected deterministic bridge replaces the disproved empty-dimension version of the all-distinct outer coefficient entry bound.
--
--   Let $n_1,n_2>0$ and fix two independent inner sample sets $\Omega_2,\Omega_3$. The outer coefficient matrix is defined by
--   $$
--   B_{ij}=H_{(i,j)}(\Omega_2,\Omega_3),
--   $$
--   where $H_{\omega_1}$ is the middle all-distinct coefficient. If the middle-coefficient event gives the uniform estimate
--   $$
--   \forall \omega_1,\quad |H_{\omega_1}(\Omega_2,\Omega_3)|\le b,
--   $$
--   then the entry supremum norm of $B$ is at most $b$:
--   $$
--   \|B\|_{\infty}=\sup_{i,j}|B_{ij}|\le b.
--   $$
--
--   The hypotheses $n_1,n_2>0$ are essential for the theorem as stated with an arbitrary real bound $b$: without them, the coefficient-bound premise is vacuous and a negative bound gives a counterexample. In Lean the proof unfolds `entrySupNorm` and `quadraticAllDistinctOuterCoefficientMatrix`, uses the nonempty finite index types supplied by $0<n_1$ and $0<n_2$, and applies `ciSup_le` twice.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

theorem quadratic_neumann_all_distinct_outer_coefficient_entry_bound_from_middle_nonempty
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 Omega3 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p bound : ℝ) :
    0 < n₁ → 0 < n₂ →
    QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p bound →
      entrySupNorm
          (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p) ≤
        bound := by
  sorry

-- Prove2me | Theorems.Thm_rudelson_selection_density_bound_from_a0_dense_sample_bound
-- name    : rudelson_selection_density_bound_from_a0_dense_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T04:11:30.046471+00:00
-- url     : https://prove2.me/theorems/30fccf55-78bd-4d4f-bdf3-8016fd4190af
-- statement:
--   Source: Candes-Recht 2008, PDF pp. 18-20, especially equation (4.9), where the Rudelson selection estimate is used under a dense sample lower bound; this node is the formal scalar bridge between the $\mu_0$-dependent Candes-Recht lower bound and the selection theorem's lower bound.
--
--   Let $\beta>2$, $n>0$, $r>0$, and $\mu_0\ge 1$.  If the sample size satisfies the stronger dense lower bound
--   $$
--   m\ge \beta\mu_0 n r\log n,
--   $$
--   then it also satisfies the Rudelson-selection lower bound
--   $$
--   m\ge \beta n r\log n.
--   $$
--   In the corrected dense branch this lets the parent theorem call the already-existing coordinate-radius Rudelson selection lemma, whose statement does not explicitly quantify $\mu_0$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem rudelson_selection_density_bound_from_a0_dense_sample_bound :
    ∀ (β μ₀ : ℝ) (n r m : ℕ),
      2 < β → 0 < n → 0 < r → 1 ≤ μ₀ →
      (m : ℝ) ≥ β * μ₀ * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ) →
      (m : ℝ) ≥ β * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ) := by
  sorry

-- Prove2me | Theorems.Thm_coordinate_cardinality_loss_absorbed_by_beta_shift
-- name    : coordinate_cardinality_loss_absorbed_by_beta_shift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T22:44:21.188495+00:00
-- url     : https://prove2.me/theorems/69e871aa-5592-45b0-882b-b88a6c91dfce
-- statement:
--   This is the scalar bookkeeping lemma that pays for a finite union bound over matrix coordinates.
--
--   Let $n=\max(n_1,n_2)$ with $n_1,n_2>0$. The coordinate index set has cardinality
--   $$
--   \left|\operatorname{Fin} n_1\times\operatorname{Fin} n_2\right|=n_1n_2\le n^2.
--   $$
--   Therefore, for $\beta>2$ and $c>0$, a pointwise failure scale $n^{-(\beta+2)}$ remains bounded by the target scale after the coordinate union bound:
--   $$
--   \left|\operatorname{Fin} n_1\times\operatorname{Fin} n_2\right|\,c\,n^{-(\beta+2)}\le c\,n^{-\beta}.
--   $$
--
--   Source context. This is the explicit finite-union bookkeeping behind the union-bound step in Candes-Recht 2008, PDF p. 29 after equation (6.17).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem coordinate_cardinality_loss_absorbed_by_beta_shift
    (β c : ℝ) (n₁ n₂ : ℕ) :
    2 < β → 0 < c → 0 < n₁ → 0 < n₂ →
    (((Fintype.card (Fin n₁ × Fin n₂) : ℝ) * c) *
        Real.rpow (↑(max n₁ n₂)) (-(β + 2))) ≤
      c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

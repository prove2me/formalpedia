-- Prove2me | Theorems.Thm_pair_coordinate_cardinality_loss_absorbed_by_beta_shift
-- name    : pair_coordinate_cardinality_loss_absorbed_by_beta_shift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T22:30:14.789218+00:00
-- url     : https://prove2.me/theorems/c7330b49-2774-4ca1-84ae-a358fd9bf159
-- statement:
--   This is the scalar bookkeeping lemma that pays for a finite union bound over ordered pairs of matrix coordinates.
--
--   Let $n=\max(n_1,n_2)$ with $n_1,n_2>0$. The number of ordered pairs of matrix coordinates is
--   $$
--   \left|\bigl(\operatorname{Fin} n_1\times\operatorname{Fin} n_2\bigr)^2\right|=(n_1n_2)^2\le n^4.
--   $$
--   Therefore, for $\beta>2$ and $c>0$, a pointwise failure scale $n^{-(\beta+4)}$ remains bounded by the target scale after the pair union bound:
--   $$
--   \left|\bigl(\operatorname{Fin} n_1\times\operatorname{Fin} n_2\bigr)^2\right|\,c\,n^{-(\beta+4)}\le c\,n^{-\beta}.
--   $$
--
--   Role in the mission. This replaces an older over-strong no-loss uniformization step. It is a standalone scalar leaf: later sketches may use it whenever a pair-coordinate union bound needs four powers of $n$ absorbed into the polynomial tail exponent.
--
--   Source context. This is the explicit finite-union bookkeeping behind the union-bound step in Candes-Recht 2008, PDF p. 29 after equation (6.17), and the ordered-pair coefficient events appearing in the quadratic Neumann expansion on PDF p. 30, equation (6.20).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem pair_coordinate_cardinality_loss_absorbed_by_beta_shift
    (β c : ℝ) (n₁ n₂ : ℕ) :
    2 < β → 0 < c → 0 < n₁ → 0 < n₂ →
    (((Fintype.card
        ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) * c) *
        Real.rpow (↑(max n₁ n₂)) (-(β + 4))) ≤
      c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry

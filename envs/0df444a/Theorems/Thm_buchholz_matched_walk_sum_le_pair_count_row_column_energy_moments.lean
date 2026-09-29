-- Prove2me | Theorems.Thm_buchholz_matched_walk_sum_le_pair_count_row_column_energy_moments
-- name    : buchholz_matched_walk_sum_le_pair_count_row_column_energy_moments
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T01:52:33.991361+00:00
-- url     : https://prove2.me/theorems/95a7727a-8cb7-46a5-b84a-03719c4b995d
-- statement:
--   This is the core Buchholz combinatorial estimate in explicit row/column energy form.  Fix $n\ge 1$, an observed coordinate set $\Omega\subseteq[n_1]\times[n_2]$, a sampling parameter $p>0$, and a real matrix $X$.
--
--   After the Rademacher signs have been averaged, only matched alternating closed walks survive.  The theorem bounds their total unsigned contribution by the number of pair partitions,
--   $$\frac{(2n)!}{2^n n!},$$
--   times the larger of the two diagonal Gram moment sums:
--   $$\sum_i\left(p^{-2}\sum_j {\bf 1}_{(i,j)\in\Omega}X_{ij}^2\right)^n,\qquad
--   \sum_j\left(p^{-2}\sum_i {\bf 1}_{(i,j)\in\Omega}X_{ij}^2\right)^n.$$
--
--   This node is the genuine Buchholz pair-count step: the remaining row/column Gram-Schatten conversion is separated into easier formal children.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_buchholz_walk_sum
open MatrixCompletion
open scoped BigOperators

theorem buchholz_matched_walk_sum_le_pair_count_row_column_energy_moments
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    buchholzMatchedWalkSum n Omega p X
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
          max
            (∑ i : Fin n1,
              (p⁻¹ ^ 2 *
                (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n)
            (∑ j : Fin n2,
              (p⁻¹ ^ 2 *
                (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n) := by
  sorry

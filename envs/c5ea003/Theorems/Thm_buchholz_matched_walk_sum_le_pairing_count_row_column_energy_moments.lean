-- Prove2me | Theorems.Thm_buchholz_matched_walk_sum_le_pairing_count_row_column_energy_moments
-- name    : buchholz_matched_walk_sum_le_pairing_count_row_column_energy_moments
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T03:01:02.529214+00:00
-- url     : https://prove2.me/theorems/628c1302-e09d-4b98-8474-c0632c239d55
-- statement:
--   Let $n\ge 1$, let $\Omega\subseteq[n_1]\times[n_2]$ be the sampled coordinate set, let $p>0$, and let $X$ be a real $n_1\times n_2$ matrix. The matched-walk sum $W_n(\Omega,p,X)$ is the unsigned contribution of alternating closed walks that survive Rademacher sign averaging.
--
--   This theorem is the Buchholz domination before evaluating the number of pairings:
--   $$
--   W_n(\Omega,p,X)\le |\mathrm{Pair}(2n)|\,\max\{R_n(\Omega,p,X),C_n(\Omega,p,X)\},
--   $$
--   where
--   $$
--   R_n=\sum_i\left(p^{-2}\sum_j {\bf 1}_{(i,j)\in\Omega}X_{ij}^2\right)^n,\qquad
--   C_n=\sum_j\left(p^{-2}\sum_i {\bf 1}_{(i,j)\in\Omega}X_{ij}^2\right)^n.
--   $$
--   The point is to isolate the genuine matched-walk comparison from the separate count $|\mathrm{Pair}(2n)|=(2n)!/(2^n n!)$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_buchholz_pairing
open MatrixCompletion
open scoped BigOperators

theorem buchholz_matched_walk_sum_le_pairing_count_row_column_energy_moments
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    buchholzMatchedWalkSum n Omega p X
      ≤ (Fintype.card (BuchholzPairing n) : ℝ) *
          max
            (∑ i : Fin n1,
              (p⁻¹ ^ 2 *
                (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n)
            (∑ j : Fin n2,
              (p⁻¹ ^ 2 *
                (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n) := by
  sorry

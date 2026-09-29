-- Prove2me | Theorems.Thm_trace_row_gram_power_eq_alternating_walk_sum
-- name    : trace_row_gram_power_eq_alternating_walk_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T01:28:52.113626+00:00
-- url     : https://prove2.me/theorems/bd4c2875-14ff-4ecf-bebd-d06e797a38b1
-- statement:
--   Let $S\in\mathbb R^{n_1\times n_2}$ and let $n\ge 1$.  The trace of the $n$-th power of the row Gram matrix $SS^\top$ expands as a closed alternating walk sum:
--   $$\operatorname{tr}\big((SS^\top)^n\big)
--   =\sum_{i:\,\mathbb Z/n\mathbb Z\to[n_1]}
--   \sum_{j:\,\mathbb Z/n\mathbb Z\to[n_2]}
--   \prod_{k\in\mathbb Z/n\mathbb Z} S_{i_k,j_k}S_{i_{k+1},j_k}.$$
--   Here the cyclic successor $k+1$ is interpreted modulo $n$.  This is the matrix-entry expansion obtained by writing the trace as a sum over row cycles and expanding each Gram entry $(SS^\top)_{i_k,i_{k+1}}=\sum_j S_{i_k,j}S_{i_{k+1},j}$.
--
--   In the Candes--Recht/Buchholz proof, this is the reusable algebraic trace expansion before the Rademacher signs are averaged.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_buchholz_signed_walk_sum
open MatrixCompletion
open scoped BigOperators

theorem trace_row_gram_power_eq_alternating_walk_sum
    (n : Nat) (hn : 1 ≤ n) {n1 n2 : Nat} (S : RealMatrix n1 n2) :
    Matrix.trace ((S * S.transpose) ^ n)
      =
    ∑ rows : Fin n → Fin n1,
      ∑ cols : Fin n → Fin n2,
        ∏ k : Fin n,
          S (rows k) (cols k) *
            S (rows (buchholzCyclicSucc k)) (cols k) := by
  sorry

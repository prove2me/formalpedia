-- Prove2me | Theorems.Thm_buchholz_matched_walk_sum_le_pair_count_gram_schatten
-- name    : buchholz_matched_walk_sum_le_pair_count_gram_schatten
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T22:58:59.876597+00:00
-- url     : https://prove2.me/theorems/e258447e-4018-450d-9f15-b4e3dfc592dc
-- statement:
--   **Buchholz matched-walk pair-count estimate.** Let $W_n(\Omega,p,X)$ be the matched-walk sum arising from the even trace moment of
--   $$S_\varepsilon=p^{-1}\sum_{(i,j)\in\Omega}\varepsilon_{ij}X_{ij}e_i e_j^{\top}.$$
--   For every integer $n\ge1$, the surviving matched-walk contribution is bounded by the number of pair partitions of $2n$ points,
--   $$\frac{(2n)!}{2^n n!},$$
--   times the larger diagonal Gram term:
--   $$W_n(\Omega,p,X)\le \frac{(2n)!}{2^n n!}\max\left\{G_{\rm row}^{2n},G_{\rm col}^{2n}\right\}.$$
--   Here $G_{\rm row}=\texttt{sampledRowGramSchatten}(\Omega,p,X,2n)$ and $G_{\rm col}=\texttt{sampledColumnGramSchatten}(\Omega,p,X,2n)$. This is the genuine Buchholz combinatorial core: after Rademacher sign survival, pairings of the $2n$ matrix factors control the closed-walk sum by the diagonal row/column Gram traces.
-- source:
--   Buchholz, A. "Operator Khintchine inequality in non-commutative probability." Math. Ann. 319 (2001): 1-16, Sections 2-3; Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119, Section 6.1 Lemma 6.1.

import Definitions.Def_buchholz_walk_sum

open MatrixCompletion
open scoped BigOperators

theorem buchholz_matched_walk_sum_le_pair_count_gram_schatten
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    buchholzMatchedWalkSum n Omega p X
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
          max ((sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))
              ((sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)) := by
  sorry

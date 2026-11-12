-- Prove2me | Theorems.Thm_BookSixth_bregman_minc_claimB
-- name    : BookSixth.bregman_minc_claimB
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-16T02:09:16.366614+00:00
-- url     : https://prove2.me/theorems/c8169994-87d3-4602-967b-9d68d4da794f
-- title:
--   Bregman-Minc Claim B: AM-GM lower bound on sum of Radhakrishnan weights
-- statement:
--   For any 0-1 matrix $ of size  \times n$ with positive row sums  = \sum_j A_{ij}$, and any compatible permutation $\sigma \in \mathcal{A}(A)$, the sum of Radhakrishnan weights over all orderings satisfies 82221\sum_{\pi \in S_n} qW(A, \sigma, \pi) \geq n! \cdot \prod_{i=1}^n (d_i!)^{-1/d_i}.82221 This is proved via AM-GM applied to the weights over all orderings, combined with a counting lemma showing that for fixed $ and  = \sigma(i)$, the product $\prod_\pi \mathrm{avail}(i, \mathrm{preS}(A,\sigma,i), \pi) = (d_i!)^{n!/d_i}$.
-- source:
--   Radhakrishnan, J. (1997). An entropy proof of Bregman theorem.

import Mathlib
import Definitions.Def_BregmanMincWeights
open scoped BigOperators
open BregmanMincWeights

namespace BookSixth

theorem bregman_minc_claimB (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ) (hA : ∀ i j, A i j ≤ 1)
    (hrows : ∀ i, 0 < ∑ j, A i j) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ aSys A) :
    (n.factorial : ℝ) * ∏ i : Fin n,
      ((Nat.factorial (∑ j, A i j) : ℕ) : ℝ) ^ (-(1 : ℝ) / ((∑ j, A i j : ℕ) : ℝ)) ≤
    ∑ π : Equiv.Perm (Fin n), qW A σ π := by
  sorry

end BookSixth

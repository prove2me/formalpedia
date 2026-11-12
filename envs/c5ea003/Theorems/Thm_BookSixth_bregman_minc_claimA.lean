-- Prove2me | Theorems.Thm_BookSixth_bregman_minc_claimA
-- name    : BookSixth.bregman_minc_claimA
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-16T02:08:39.105304+00:00
-- url     : https://prove2.me/theorems/89fed46f-e59d-4842-8051-e2b9e980c9cd
-- title:
--   Bregman-Minc Claim A: sum of Radhakrishnan weights ≤ 1
-- statement:
--   For any 0-1 matrix $ of size  \times n$ with positive row sums and any permutation $\pi$ of the rows, the sum of Radhakrishnan weights $\sum_{\sigma \in \mathcal{A}(A)} qW(A, \sigma, \pi) \leq 1$. Here $\mathcal{A}(A)$ is the set of compatible permutations (A-systems) and (A,\sigma,\pi) = \prod_i 1/\mathrm{avail}(i, \mathrm{preS}(A,\sigma,i), \pi)$.
-- source:
--   Radhakrishnan, J. (1997). An entropy proof of Bregman theorem. See also Friedland, S. (2010). A proof of a generalized van der Waerden conjecture.

import Mathlib
import Definitions.Def_BregmanMincWeights
open scoped BigOperators
open BregmanMincWeights

namespace BookSixth

theorem bregman_minc_claimA : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ)
    (hA : ∀ i j, A i j ≤ 1) (hrows : ∀ i, 0 < ∑ j, A i j)
    (π : Equiv.Perm (Fin n)), ∑ σ ∈ aSys A, qW A σ π ≤ 1 := by
  sorry

end BookSixth

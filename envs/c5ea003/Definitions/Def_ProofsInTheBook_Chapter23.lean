-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter23
-- name    : ProofsInTheBook_Chapter23
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T15:57:02.816527+00:00
-- url     : https://prove2.me/theorems/6ee53563-7ff6-4a3e-8c6d-389dec210549
-- title:
--   Subset sums in a half-open interval
-- statement:
--   For real weights $a_0,\ldots,a_{n-1}$ and a subset S of their index set, define
--   $$s_a(S)=\sum_{i\in S}a_i.$$
--   For a real x, define the family
--   $$\mathcal F(a,x)=\{S\subseteq\{0,\ldots,n-1\}:x\le s_a(S)<x+1\}.$$
--   The empty subset is allowed and has sum zero. These definitions impose no sign or magnitude restriction on the weights; hypotheses such as $a_i\ge1$ belong to subsequent theorems.
-- source:
--   Mathematical definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter23.lean#L31. Topic: Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 25, “On a lemma of Littlewood and Offord” (https://doi.org/10.1007/978-3-662-57265-8_25). The repository citation specifies the definitions retained here.

import Mathlib

/-!
# Chapter 23: On a lemma of Littlewood and Offord

From "Proofs from THE BOOK":

**Littlewood-Offord lemma**: Among all 2ⁿ sums ±a₁ ± a₂ ± ⋯ ± aₙ
(with |aᵢ| ≥ 1), at most C(n, ⌊n/2⌋) lie in any interval of length 2.

The book presents Erdős's elegant proof using Dilworth's theorem
(or the LYM inequality) to bound antichains in the power set.
-/

namespace ProofsInTheBook.Chapter23

open Finset

noncomputable section

/-!
### Erdős's reduction to Sperner

We formalize the standard subset-sum form used in the Littlewood-Offord proof.
If every weight is at least `1`, then two comparable subsets have sums differing
by at least `1`. Hence all subsets whose sums lie in the same half-open interval
`[x, x + 1)` form an antichain, and Sperner's theorem gives the middle-layer
bound.
-/

def subsetSum {n : ℕ} (a : Fin n → ℝ) (s : Finset (Fin n)) : ℝ :=
  ∑ i ∈ s, a i

def shortIntervalSubsetSums {n : ℕ} (a : Fin n → ℝ) (x : ℝ) : Finset (Finset (Fin n)) :=
  (Finset.univ.powerset.filter fun s => x ≤ subsetSum a s ∧ subsetSum a s < x + 1)











end

end ProofsInTheBook.Chapter23



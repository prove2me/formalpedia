-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter29_chapter29
-- name    : ProofsInTheBook.Chapter29.chapter29
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:11:39.558799+00:00
-- url     : https://prove2.me/theorems/5ec5d6a0-a81e-4668-881f-8ba4486f33e2
-- title:
--   GSR shuffle distribution via compatible label counts
-- statement:
--   Let $a,n\in\mathbb N$ with $a>0$. Choose a labeling $\ell:\operatorname{Fin}(n)\to\operatorname{Fin}(a)$ uniformly from its $a^n$ possibilities and stably sort the cards by label, obtaining `riffleSort`. Let $P_{a,n}(\sigma)$ be the resulting probability of a permutation $\sigma$. Let $C_{a,n}(\sigma)$ denote `rifflePatternCount a n (riffleDescentIntervalPattern n σ)`, the finite count of sorted label sequences compatible with the encoded descent-interval pattern. Then
--   $$P_{a,n}(\sigma)=\frac{C_{a,n}(\sigma)}{a^n}\quad(\sigma\in S_n),\qquad\sum_{\sigma\in S_n}P_{a,n}(\sigma)=1.$$
--   Probabilities are represented in the nonnegative rationals.
--
--   This identifies the stable-sort distribution by compatible-label counts. No closed binomial expression or mixing-time estimate is asserted.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 31, “Shuffling cards”, pp. 219–228 (https://doi.org/10.1007/978-3-662-57265-8_31). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter29.lean#L523. The chapter reference identifies the topic; it does not claim the Lean development reproduces every argument of that chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter29
open ProofsInTheBook.Chapter29

theorem ProofsInTheBook.Chapter29.chapter29 (a n : ℕ) [NeZero a] :
    (∀ σ : Equiv.Perm (Fin n),
      gsrShuffleProbability a n σ =
        (rifflePatternCount a n (riffleDescentIntervalPattern n σ) : ℚ≥0) /
          ((a ^ n : ℕ) : ℚ≥0)) ∧
      (∑ σ : Equiv.Perm (Fin n), gsrShuffleProbability a n σ) = 1 := by sorry

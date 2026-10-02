-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter17_chapter17_cantor
-- name    : ProofsInTheBook.Chapter17.chapter17_cantor
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T15:17:24.613833+00:00
-- url     : https://prove2.me/theorems/cafb7121-8358-4054-a0ff-d2ea47d40d60
-- title:
--   Cantor’s theorem: no surjection onto the power set
-- statement:
--   For every set $A$ and every function $f:A\to\mathcal P(A)$, the function $f$ is not surjective:
--   $$\neg\bigl(\forall B\subseteq A,\ \exists a\in A,\ f(a)=B\bigr).$$
--   There is no finiteness, nonemptiness, or countability assumption on $A$. Here $\mathcal P(A)$ is the set of all subsets of $A$.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 19, “Sets, functions, and the continuum hypothesis”, pp. 127–142 (https://doi.org/10.1007/978-3-662-57265-8_19). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter17.lean#L29. The book citation identifies the topic; the selected declaration does not claim to reproduce the entire chapter.

import Mathlib

theorem ProofsInTheBook.Chapter17.chapter17_cantor {α : Type*} (f : α → Set α) :
    ¬ Function.Surjective f := by sorry

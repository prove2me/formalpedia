-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter37_chapter37
-- name    : ProofsInTheBook.Chapter37.chapter37
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:11:10.34862+00:00
-- url     : https://prove2.me/theorems/b8397150-2af8-4b95-bf0b-5a343010fb13
-- title:
--   Turán’s extremal graph theorem with uniqueness
-- statement:
--   Let $n,r\in\mathbb N$ with $r>0$, and let $T(n,r)$ be the balanced complete $r$-partite graph on $\operatorname{Fin}(n)$. It is $K_{r+1}$-free and has at least as many edges as every $K_{r+1}$-free simple graph on that vertex set. Moreover, for every such finite-indexed simple graph $G$ with decidable adjacency,
--   $$\bigl(G\text{ is }K_{r+1}\text{-free}\ \land\ |E(G)|=|E(T(n,r))|\bigr)\quad\Longleftrightarrow\quad G\cong T(n,r).$$
--
--   This includes extremality and uniqueness up to graph isomorphism. The local proof uses Mathlib’s Turán theorem and its isomorphism API.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 41, “Turán’s graph theorem”, pp. 285–289 (https://doi.org/10.1007/978-3-662-57265-8_41). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter37.lean#L83. The chapter reference identifies the topic; it does not claim the Lean development reproduces every argument of that chapter.

import Mathlib
open SimpleGraph

theorem ProofsInTheBook.Chapter37.chapter37 (n r : ℕ) (hr : 0 < r) :
    (turanGraph n r).IsTuranMaximal r ∧
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.CliqueFree (r + 1) ∧
            Finset.card G.edgeFinset = Finset.card (turanGraph n r).edgeFinset ↔
          Nonempty (G ≃g turanGraph n r) := by sorry

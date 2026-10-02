-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter36_chapter36_artgallery_combinatorial
-- name    : ProofsInTheBook.Chapter36.chapter36_artgallery_combinatorial
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:41:15.038016+00:00
-- url     : https://prove2.me/theorems/7f73cac4-732a-4713-84be-28a3b2c49b4e
-- title:
--   A small vertex set meeting every triangle in an inductive triangulation
-- statement:
--   Let $n\in\mathbb N$, and let $S$ be a finite set of abstract triangles, each an ordered triple of distinct vertices in $\operatorname{Fin}(n)$. Assume `TriangulatedPolygon n S`: one starts with a single triangle and repeatedly adds a triangle sharing an existing edge, with its third vertex absent from every earlier triangle. There exists a set $G\subseteq\operatorname{Fin}(n)$ such that
--   $$|G|\le\lfloor n/3\rfloor,\qquad\forall T\in S,\quad G\cap\{T.a,T.b,T.c\}\ne\varnothing.$$
--   The ambient index set may contain unused vertices.
--
--   This is a finite combinatorial hitting-set bound. It does not assert geometric visibility or the existence of a triangulation for an arbitrary simple plane polygon.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 40, “How to guard a museum”, pp. 281–284 (https://doi.org/10.1007/978-3-662-57265-8_40). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter36.lean#L297. The book citation identifies the topic; the selected declaration has only the scope stated above.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter36
open ProofsInTheBook.Chapter36
open GuardColor

theorem ProofsInTheBook.Chapter36.chapter36_artgallery_combinatorial {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ T ∈ S, ∃ v ∈ guards,
        v ∈ ({T.a, T.b, T.c} : Finset (Fin n)) := by sorry

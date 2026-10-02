-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter36_TriangulatedPolygon_exists_3coloring
-- name    : ProofsInTheBook.Chapter36.TriangulatedPolygon.exists_3coloring
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:40:51.340467+00:00
-- url     : https://prove2.me/theorems/442ae0cd-927a-4d2c-828d-e218f08c780c
-- title:
--   Three-coloring an inductively attached triangle family
-- statement:
--   Let $n\in\mathbb N$, and let $S$ be a finite set of ordered triples of distinct vertices of $\operatorname{Fin}(n)$, regarded as abstract triangles. Assume `TriangulatedPolygon n S`: $S$ is formed from one triangle by repeatedly adding a triangle with a fresh third vertex and an edge shared with a triangle already present. Then there exists a coloring $c:\operatorname{Fin}(n)\to\{\mathrm{red},\mathrm{green},\mathrm{blue}\}$ such that
--   $$\forall T\in S,\quad c(T.a)\ne c(T.b),\quad c(T.b)\ne c(T.c),\quad c(T.a)\ne c(T.c).$$
--   The color assignment includes unused ambient vertices.
--
--   This is a combinatorial coloring theorem, with the inductive triangle-family input retained; no plane embedding is asserted.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 40, “How to guard a museum”, pp. 281–284 (https://doi.org/10.1007/978-3-662-57265-8_40). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter36.lean#L132. The book citation identifies the topic; the selected declaration has only the scope stated above.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter36
open ProofsInTheBook.Chapter36
open GuardColor

theorem ProofsInTheBook.Chapter36.TriangulatedPolygon.exists_3coloring {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) :
    ∃ c : Fin n → GuardColor,
      ∀ T ∈ S, c T.a ≠ c T.b ∧ c T.b ≠ c T.c ∧ c T.a ≠ c T.c := by sorry

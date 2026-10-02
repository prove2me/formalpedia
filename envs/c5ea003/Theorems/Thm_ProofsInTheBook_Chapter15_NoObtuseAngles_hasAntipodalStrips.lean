-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter15_NoObtuseAngles_hasAntipodalStrips
-- name    : ProofsInTheBook.Chapter15.NoObtuseAngles.hasAntipodalStrips
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T15:38:35.287092+00:00
-- url     : https://prove2.me/theorems/1b2efd9c-b6bd-4bea-a730-408aff3a9713
-- title:
--   A non-obtuse point set lies between perpendicular supporting hyperplanes
-- statement:
--   Let $d\in\mathbb N$ and let $S\subseteq\mathbb R^d$ be finite. Suppose that every three pairwise distinct points $x,y,z\in S$ satisfy $\langle x-z,y-z\rangle\ge0$. Then for every pair of distinct points $a,b\in S$ and every $x\in S$,
--   $$0\le\langle b-a,x-a\rangle\le\|b-a\|^2.$$
--   The inner product and norm are Euclidean. Equivalently, $S$ lies in the closed strip bounded by the hyperplanes through $a$ and $b$ perpendicular to $b-a$.
--
--   This is the supporting-strip lemma used to derive the point-count bound.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 17, “Every large point set has an obtuse angle”, pp. 111–116 (https://doi.org/10.1007/978-3-662-57265-8_17). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter15.lean#L439. The book citation identifies the topic; this local supporting declaration need not be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter15
open scoped ENNReal RealInnerProductSpace
open MeasureTheory
open ProofsInTheBook.Chapter15

theorem ProofsInTheBook.Chapter15.NoObtuseAngles.hasAntipodalStrips {d : ℕ} {points : Finset (Point d)}
    (hno : NoObtuseAngles points) : HasAntipodalStrips points := by sorry

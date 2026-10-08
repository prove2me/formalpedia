-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter15_antipodal_card_bound
-- name    : ProofsInTheBook.Chapter15.antipodal_card_bound
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T15:38:52.033782+00:00
-- url     : https://prove2.me/theorems/2e183938-a043-4fc2-8c20-01bb57b62f51
-- title:
--   The cardinality bound for perpendicular antipodal strips
-- statement:
--   Let $d\in\mathbb N$ and let $S\subseteq\mathbb R^d$ be finite. Suppose that for every distinct $a,b\in S$ and every $x\in S$,
--   $$0\le\langle b-a,x-a\rangle\le\|b-a\|^2.$$
--   Thus each pair determines perpendicular supporting hyperplanes containing $S$ between them. Then
--   $$|S|\le2^d.$$
--   The set may be empty and need not span the ambient Euclidean space; no positive-volume assumption is retained.
--
--   This is the cardinality estimate used in the obtuse-angle theorem, for the precise perpendicular-strip hypothesis encoded in the development.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 17, “Every large point set has an obtuse angle”, pp. 111–116 (https://doi.org/10.1007/978-3-662-57265-8_17). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter15.lean#L380. The book citation identifies the topic; this local supporting declaration need not be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter15
open scoped ENNReal RealInnerProductSpace
open MeasureTheory
open ProofsInTheBook.Chapter15

theorem ProofsInTheBook.Chapter15.antipodal_card_bound {d : ℕ} (points : Finset (Point d))
    (hanti : HasAntipodalStrips points) : points.card ≤ 2 ^ d := by sorry

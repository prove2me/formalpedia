-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter15_chapter15
-- name    : ProofsInTheBook.Chapter15.chapter15
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T15:39:07.754076+00:00
-- url     : https://prove2.me/theorems/1f0b98da-4843-4764-95c0-587f8dace556
-- title:
--   More than 2^d Euclidean points determine an obtuse angle
-- statement:
--   Let $d\in\mathbb N$ and let $S\subseteq\mathbb R^d$ be a finite set with $|S|>2^d$. Then there exist pairwise distinct points $x,y,z\in S$ such that
--   $$\langle x-z,y-z\rangle<0.$$
--   The inner product is Euclidean, so the angle at $z$ determined by $x$ and $y$ is strictly greater than $\pi/2$.
--
--   This is the obtuse-angle existence theorem for an arbitrary finite point set in the stated dimension.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 17, “Every large point set has an obtuse angle”, pp. 111–116 (https://doi.org/10.1007/978-3-662-57265-8_17). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter15.lean#L480. The book citation identifies the topic; the selected declaration does not claim to reproduce the entire chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter15
open scoped ENNReal RealInnerProductSpace
open MeasureTheory
open ProofsInTheBook.Chapter15

theorem ProofsInTheBook.Chapter15.chapter15 {d : ℕ} (points : Finset (Point d)) (hcard : 2 ^ d < points.card) :
    ∃ x ∈ points, ∃ y ∈ points, ∃ z ∈ points,
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ ObtuseTriple x y z := by sorry

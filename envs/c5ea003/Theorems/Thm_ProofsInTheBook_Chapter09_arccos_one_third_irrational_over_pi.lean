-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter09_arccos_one_third_irrational_over_pi
-- name    : ProofsInTheBook.Chapter09.arccos_one_third_irrational_over_pi
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T15:38:39.319334+00:00
-- url     : https://prove2.me/theorems/55e441ab-b086-4fa6-bde1-ca28abc2a9a5
-- title:
--   The angle arccos(1/3) is not a rational multiple of π
-- statement:
--   For every rational number $q$,
--   $$\arccos(1/3)\ne q\pi.$$
--   Here $\arccos$ is the real principal inverse cosine and $\pi$ is the usual circle constant. There are no additional hypotheses on $q$.
--
--   This supplies the nonzero angle class needed for the coordinate tetrahedron’s rational Dehn invariant.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 10, “Hilbert’s third problem: decomposing polyhedra”, pp. 67–75 (https://doi.org/10.1007/978-3-662-57265-8_10). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter09.lean#L1114. The book citation identifies the topic; this local supporting declaration need not be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter09
open scoped BigOperators TensorProduct
open Polynomial Chebyshev
open ProofsInTheBook.Chapter09

theorem ProofsInTheBook.Chapter09.arccos_one_third_irrational_over_pi (q : ℚ) :
    Real.arccos (1/3) ≠ q * Real.pi := by sorry

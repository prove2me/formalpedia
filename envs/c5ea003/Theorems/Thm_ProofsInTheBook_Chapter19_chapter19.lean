-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter19_chapter19
-- name    : ProofsInTheBook.Chapter19.chapter19
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:10:52.424589+00:00
-- url     : https://prove2.me/theorems/a337a994-84eb-48d9-b820-29c83f0746a7
-- title:
--   Every nonconstant complex polynomial has a root
-- statement:
--   Let $p\in\mathbb C[X]$ satisfy $p.\mathrm{natDegree}\ge1$. Then there exists $z\in\mathbb C$ such that
--   $$p(z)=0.$$
--   The degree condition excludes both constant polynomials and the zero polynomial, whose natural degree in Lean is zero. No restriction is placed on the complex coefficients.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 21, “The fundamental theorem of algebra”, pp. 151–153 (https://doi.org/10.1007/978-3-662-57265-8_21). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter19.lean#L307. The citation identifies the topic, not complete formalization of every result in that chapter.

import Mathlib.Topology.Algebra.Polynomial
import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter19
open Polynomial Bornology
open ProofsInTheBook.Chapter19

theorem ProofsInTheBook.Chapter19.chapter19 (p : ℂ[X]) (hdeg : 1 ≤ p.natDegree) : ∃ z : ℂ, p.eval z = 0 := by sorry

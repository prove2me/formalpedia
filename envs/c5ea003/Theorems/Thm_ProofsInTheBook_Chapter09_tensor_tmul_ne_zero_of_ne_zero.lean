-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter09_tensor_tmul_ne_zero_of_ne_zero
-- name    : ProofsInTheBook.Chapter09.tensor_tmul_ne_zero_of_ne_zero
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T15:38:37.688749+00:00
-- url     : https://prove2.me/theorems/8de53496-cc97-4551-beb7-5bd7d1f15723
-- title:
--   A pure tensor of nonzero vectors over a field is nonzero
-- statement:
--   Let $K$ be a field, let $M$ and $N$ be vector spaces over $K$, and let $m\in M$ and $n\in N$ satisfy $m\ne0$ and $n\ne0$. Then
--   $$m\otimes_K n\ne0\quad\text{in }M\otimes_K N.$$
--   Neither vector space is required to be finite-dimensional.
--
--   This algebraic helper converts a nonzero edge-length factor and a nonzero angle class into a nonzero Dehn tensor.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 10, “Hilbert’s third problem: decomposing polyhedra”, pp. 67–75 (https://doi.org/10.1007/978-3-662-57265-8_10). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter09.lean#L1218. The book citation identifies the topic; this local supporting declaration need not be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter09
open scoped BigOperators TensorProduct
open Polynomial Chebyshev
open ProofsInTheBook.Chapter09

theorem ProofsInTheBook.Chapter09.tensor_tmul_ne_zero_of_ne_zero {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {m : M} {n : N} (hm : m ≠ 0) (hn : n ≠ 0) :
    (m ⊗ₜ[K] n : TensorProduct K M N) ≠ 0 := by sorry

-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter40_chapter40
-- name    : ProofsInTheBook.Chapter40.chapter40
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:41:35.758932+00:00
-- url     : https://prove2.me/theorems/451ec463-d71a-4917-a998-0dbe03a8b32c
-- title:
--   The friendship theorem
-- statement:
--   Let G be a simple undirected graph on a finite nonempty vertex set V. Suppose every two distinct vertices have exactly one common neighbor, whether or not those two vertices are adjacent. Then there is a vertex v adjacent to every other vertex:
--   $$\exists v\in V\ \forall w\in V,\quad w\ne v\Longrightarrow v\sim w.$$
--   No degree regularity is assumed.
-- source:
--   Repository endpoint: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter40.lean#L36. Archive authors: Aaron Anderson, Jalex Stark, and Kyle Miller; Apache 2.0 license retained. The proof used by this endpoint comes from Mathlib Archive at commit c5ea00351c28e24afc9f0f84379aa41082b1188f. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 44, “Of friends and politicians”, pp. 307–309 (https://doi.org/10.1007/978-3-662-57265-8_44).

import Init
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib
import Definitions.Def_P2MAssembly_Chapter40
open ProofsInTheBook.Chapter40
open SimpleGraph Theorems100

theorem ProofsInTheBook.Chapter40.chapter40 {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : Friendship G) : ExistsPolitician G := by sorry

-- Prove2me | Theorems.Thm_BookSixth_round_circle_unlink_empty
-- name    : BookSixth.round_circle_unlink_empty
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T20:52:10.237312+00:00
-- url     : https://prove2.me/theorems/1dcd7c15-29f7-45a1-a383-065b04e79dcc
-- title:
--   Chapter 15 bridge: the empty family is an unlink
-- statement:
--   The empty ordered family of components is an unlink. This is the base case for the finite round-circle induction in Chapter 15, Theorem 1.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Base-case adapter for BookSixth.round_circle_unlink. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_unlink_empty : IsUnlink (fun _ : Fin 0 => (∅ : Set Space3)) := by sorry

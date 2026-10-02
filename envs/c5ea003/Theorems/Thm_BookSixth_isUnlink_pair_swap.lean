-- Prove2me | Theorems.Thm_BookSixth_isUnlink_pair_swap
-- name    : BookSixth.isUnlink_pair_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T07:50:29.975649+00:00
-- url     : https://prove2.me/theorems/fd9760e4-d5e6-4993-982a-4ed5ae248fa6
-- title:
--   Chapter 15 bridge: exchange the order of an unlinked pair
-- statement:
--   If the ordered two-component family $[A,B]$ is an unlink, then the reversed ordered family $[B,A]$ is also an unlink.
--
--   The witness for $[A,B]$ can be composed with a continuous ambient half-turn exchanging the two standard circles. This changes the ordered target pair from $(\operatorname{standardCircle}0,\operatorname{standardCircle}1)$ to $(\operatorname{standardCircle}1,\operatorname{standardCircle}0)$ while preserving continuity of both the isotopy and its inverse.
--
--   This is the finite order-reversal step used when two components of a larger family are tested against an appended circle.
--
--   **Formalization Note.** The statement is order-sensitive: the input and output are two-element indexed families, not unordered subsets.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Finite order-reversal of a two-component unlink certificate, derived by composing its witness with the standard half-turn exchanging the two standard circles. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.isUnlink_pair_swap {A B : Set Space3}
    (h : IsUnlink (![A, B] : Fin 2 → Set Space3)) :
    IsUnlink (![B, A] : Fin 2 → Set Space3) := by sorry

-- Prove2me | Theorems.Thm_BookSixth_round_circle_unlink
-- name    : BookSixth.round_circle_unlink
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-13T01:37:54.443889+00:00
-- url     : https://prove2.me/theorems/2468ff3e-d023-401f-9c43-3f1e9c88283d
-- title:
--   Chapter 15, Theorem 1: pairwise unlinked round circles
-- statement:
--   Any finite collection of disjoint geometric round circles in real three-space is an unlink if each pair is an unlink. Here unlink means that an ambient isotopy, continuous together with its inverse, carries the ordered components to separated standard unit circles. It does not mean arbitrary loops are unlinked merely because pairs are.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1: pairwise unlinked round circles, p. 100. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_unlink {m : ℕ} (C : Fin m → Set Space3) (hround : ∀ i, RoundCircle (C i)) (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hpairs : ∀ i j, i ≠ j → IsUnlink (![C i, C j] : Fin 2 → Set Space3)) :
    IsUnlink C := by sorry

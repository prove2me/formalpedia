-- Prove2me | Theorems.Thm_BookSixth_round_circle_unlink_snoc
-- name    : BookSixth.round_circle_unlink_snoc
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T20:51:50.912562+00:00
-- url     : https://prove2.me/theorems/6181fc76-d41a-4748-8d50-a774894885bd
-- title:
--   Chapter 15 bridge: append a disjoint round circle to an unlinked family
-- statement:
--   Geometric append lemma for Chapter 15, Theorem 1: if a finite family of disjoint round circles is already an unlink, and a further disjoint round circle is an unlink with every existing circle, then the family with the new circle appended is an unlink. This isolates the ambient-isotopy composition step; it is not assumed by the parent theorem.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Source-faithful append lemma for BookSixth.round_circle_unlink. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_unlink_snoc {n : ℕ} (C : Fin n → Set Space3) (D : Set Space3)
    (hroundC : ∀ i, RoundCircle (C i)) (hroundD : RoundCircle D)
    (hdisjointC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hdisjointD : ∀ i, Disjoint (C i) D)
    (hprefix : IsUnlink C)
    (hpairs : ∀ i, IsUnlink (![C i, D] : Fin 2 → Set Space3)) :
    IsUnlink (Fin.snoc C D) := by sorry

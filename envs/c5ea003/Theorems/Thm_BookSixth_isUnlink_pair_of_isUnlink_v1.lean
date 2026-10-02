-- Prove2me | Theorems.Thm_BookSixth_isUnlink_pair_of_isUnlink_v1
-- name    : BookSixth.isUnlink_pair_of_isUnlink_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T13:14:51.399066+00:00
-- url     : https://prove2.me/theorems/0e05058c-b2b1-4b2a-b993-b8c5d5ae59fa
-- title:
--   Chapter 15 bridge: extract a two-component unlink certificate
-- statement:
--   If an ordered finite family is an unlink, then any two distinct members, in their inherited order, are also an unlink. The witness for the larger family gives an ambient isotopy to the assigned standard circles; the missing step is a source-faithful finite relabeling of the two standard-circle targets back to the two standard circles indexed by 0 and 1.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Finite pair extraction from the ambient-isotopy definition of an unlink. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.isUnlink_pair_of_isUnlink_v1 {n : ℕ} (C : Fin n → Set Space3) (hC : IsUnlink C) (i j : Fin n) (hij : i ≠ j) : IsUnlink (![C i, C j] : Fin 2 → Set Space3) := by sorry

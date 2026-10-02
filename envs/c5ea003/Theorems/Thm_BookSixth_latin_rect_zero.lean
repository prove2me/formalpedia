-- Prove2me | Theorems.Thm_BookSixth_latin_rect_zero
-- name    : BookSixth.latin_rect_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T04:04:11.553739+00:00
-- url     : https://prove2.me/theorems/72ab5f36-2f20-48a8-afb0-af019aac6ead
-- title:
--   Chapter 37 bridge: the empty Latin rectangle is unique
-- statement:
--   There is exactly one 0-row Latin rectangle: all row/column conditions hold vacuously.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.latin_rect_zero (n : ℕ) :
    (Finset.univ.filter (fun R : Fin 0 → Fin n → Fin n =>
      (∀ i, Function.Bijective (R i)) ∧ (∀ j, Function.Injective (fun i => R i j)))).card
    = 1 := by sorry

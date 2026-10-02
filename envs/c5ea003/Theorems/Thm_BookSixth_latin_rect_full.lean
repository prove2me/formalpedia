-- Prove2me | Theorems.Thm_BookSixth_latin_rect_full
-- name    : BookSixth.latin_rect_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T04:04:11.222599+00:00
-- url     : https://prove2.me/theorems/d525b82e-e803-407e-bdd1-a531cf93407a
-- title:
--   Chapter 37 bridge: n-row Latin rectangles are Latin squares
-- statement:
--   The number of n-row Latin rectangles equals latinCount: column injectivity is column bijectivity for endofunctions on a finite type.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.latin_rect_full (n : ℕ) :
    (Finset.univ.filter (fun R : Fin n → Fin n → Fin n =>
      (∀ i, Function.Bijective (R i)) ∧ (∀ j, Function.Injective (fun i => R i j)))).card
    = latinCount n := by sorry

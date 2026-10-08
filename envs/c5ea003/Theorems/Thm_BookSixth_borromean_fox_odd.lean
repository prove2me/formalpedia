-- Prove2me | Theorems.Thm_BookSixth_borromean_fox_odd
-- name    : BookSixth.borromean_fox_odd
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-13T01:37:23.834842+00:00
-- url     : https://prove2.me/theorems/b9619dc5-51be-4349-87a8-2d8b071a4e61
-- title:
--   Chapter 15, Theorem 2 proof: odd Fox colorings
-- statement:
--   For every odd modulus n at least 3, the Fox crossing equations of the standard Borromean diagram force all three outer labels to agree, and conversely constant labels satisfy them. Inner labels are determined by the outer crossing equations. This is the diagram calculation used in Theorem 2; by itself it is not a theorem about ambient isotopy.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 2 proof: odd Fox colorings, p. 104. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.borromean_fox_odd (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) (a b c : ZMod n) :
    BorromeanFox a b c ↔ a = b ∧ b = c := by sorry

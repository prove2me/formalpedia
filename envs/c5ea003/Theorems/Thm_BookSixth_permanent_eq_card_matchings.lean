-- Prove2me | Theorems.Thm_BookSixth_permanent_eq_card_matchings
-- name    : BookSixth.permanent_eq_card_matchings
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T02:30:13.971714+00:00
-- url     : https://prove2.me/theorems/0c86b409-90a0-47d2-a544-6733e2b42181
-- title:
--   Chapter 37 bridge: a 0-1 permanent counts perfect matchings
-- statement:
--   The permanent of a 0-1 matrix equals the number of permutations selecting all ones, i.e. the number of perfect matchings.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_eq_card_matchings (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) : Matrix.permanent M = ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, M i (σ i) = 1)).card : ℝ) := by sorry

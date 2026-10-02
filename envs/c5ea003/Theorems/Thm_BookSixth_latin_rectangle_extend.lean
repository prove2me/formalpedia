-- Prove2me | Theorems.Thm_BookSixth_latin_rectangle_extend
-- name    : BookSixth.latin_rectangle_extend
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T03:28:01.939981+00:00
-- url     : https://prove2.me/theorems/efd2bcc3-4c8f-4f2f-9de4-f2cc75eb25a0
-- title:
--   Chapter 37 bridge: Latin rectangle counts factor through row extensions
-- statement:
--   The number of (k+1)-row Latin rectangles equals the sum over k-row rectangles of the number of valid next rows (permutations avoiding each column's used symbols).
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.latin_rectangle_extend (n k : ℕ) (hkn : k < n) :
    (Finset.univ.filter (fun R : Fin (k + 1) → Fin n → Fin n =>
      (∀ i, Function.Bijective (R i)) ∧ (∀ j, Function.Injective (fun i => R i j)))).card
    = ∑ R ∈ Finset.univ.filter (fun R : Fin k → Fin n → Fin n =>
      (∀ i, Function.Bijective (R i)) ∧ (∀ j, Function.Injective (fun i => R i j))),
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        ∀ j, ∀ i : Fin k, R i j ≠ σ j)).card := by sorry

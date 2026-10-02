-- Prove2me | Theorems.Thm_BookSixth_rectangle_extension_lower
-- name    : BookSixth.rectangle_extension_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T02:43:11.475983+00:00
-- url     : https://prove2.me/theorems/05a2e61b-8bfe-46ff-878d-863426c563ca
-- title:
--   Chapter 37 bridge: rectangle extensions satisfy the van der Waerden step bound
-- statement:
--   With k symbols used per row and column, the number of valid next rows is at least (n-k)^n (n!/n^n) via van der Waerden on the availability matrix.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.rectangle_extension_lower (n k : ℕ) (hkn : k ≤ n) (used : Fin n → Finset (Fin n)) (hcard : ∀ i, (used i).card = k) (hcol : ∀ s, (Finset.univ.filter (fun i => s ∈ used i)).card = k) (hvdW : (∀ (A : Matrix (Fin n) (Fin n) ℝ), (∀ i j, 0 ≤ A i j) → (∀ i, ∑ j, A i j = 1) → (∀ j, ∑ i, A i j = 1) → (n.factorial : ℝ) / (n : ℝ) ^ n ≤ Matrix.permanent A)) : ((((n - k : ℕ)) : ℝ) ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n) ≤ ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∉ used i)).card : ℝ)) := by sorry

-- Prove2me | Theorems.Thm_BookSixth_rectangle_extension_upper
-- name    : BookSixth.rectangle_extension_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T02:43:29.079294+00:00
-- url     : https://prove2.me/theorems/8f7a8302-3d2e-4194-94fa-973e2b67f822
-- title:
--   Chapter 37 bridge: rectangle extensions satisfy the Bregman-Minc step bound
-- statement:
--   With k symbols used per column, the number of valid next rows is at most ((n-k)!)^(n/(n-k)) via Bregman-Minc on the availability matrix.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.rectangle_extension_upper (n k : ℕ) (hkn : k ≤ n) (used : Fin n → Finset (Fin n)) (hcard : ∀ i, (used i).card = k) (hBM : (∀ (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℕ), (∀ i j, A i j = 0 ∨ A i j = 1) → (∀ i, ∑ j, A i j = (r i : ℝ)) → Matrix.permanent A ≤ ∏ i, ((r i).factorial : ℝ) ^ ((1 : ℝ) / (r i : ℝ)))) : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ∉ used i)).card : ℝ) ≤ ∏ _i : Fin n, ((((n - k).factorial : ℕ) : ℝ) ^ ((1 : ℝ) / (((n - k : ℕ)) : ℝ))) := by sorry

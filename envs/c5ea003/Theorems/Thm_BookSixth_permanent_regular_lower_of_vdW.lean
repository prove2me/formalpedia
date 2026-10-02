-- Prove2me | Theorems.Thm_BookSixth_permanent_regular_lower_of_vdW
-- name    : BookSixth.permanent_regular_lower_of_vdW
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T01:28:28.225988+00:00
-- url     : https://prove2.me/theorems/1d729a3b-9c70-4e13-8b56-d46dbcaff359
-- title:
--   Chapter 37 bridge: regular permanent bound from van der Waerden
-- statement:
--   Conditional van der Waerden corollary: if every doubly stochastic $n \times n$ matrix has permanent at least $n!/n^n$, then a 0-1 matrix with all row and column sums $d$ has permanent at least $d^n \cdot n!/n^n$. This is the row-extension estimate behind the lower counting bound of Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Theorem 2 row-extension estimate, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_regular_lower_of_vdW (n : ℕ) (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℝ) (d : ℕ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hrow : ∀ i, ∑ j, M i j = (d : ℝ)) (hcol : ∀ j, ∑ i, M i j = (d : ℝ))
    (hvdW : ∀ (A : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j, 0 ≤ A i j) → (∀ i, ∑ j, A i j = 1) → (∀ j, ∑ i, A i j = 1) →
      (n.factorial : ℝ) / (n : ℝ) ^ n ≤ Matrix.permanent A) :
    (d : ℝ) ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n) ≤ Matrix.permanent M := by sorry
